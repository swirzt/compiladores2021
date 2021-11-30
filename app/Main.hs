{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)
import Data.List (nub,  intersperse, isPrefixOf )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )

import System.Exit
--import System.Process ( system )
import Options.Applicative
--import Data.Text.Lazy (unpack)

import Global ( GlEnv(..) )
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, desugarDecl, desugarTy )
import Eval ( eval )
import PPrint
import MonadFD4
import TypeChecker ( tc, tcDecl, tcDeclTy )
import CEK
import Bytecompile (bytecompileModule, bcWrite, bcRead, runBC)
import System.FilePath.Windows (replaceExtension)
import ClosureConvert
import Optimizations

prompt :: String
prompt = "FD4> "

{- 
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | InteractiveCEK
  | Bytecompile 
  | RunVM
  | CC
  -- | Canon
  -- | LLVM
  -- | Build

-- | Parser de banderas
parseMode :: Parser (Mode,Bool)
parseMode = (,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' LLVM ( long "llvm" <> short 'l' <> help "Imprimir LLVM resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
  --  <*> pure False
   -- reemplazar por la siguiente línea para habilitar opción
    <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool, [FilePath])
parseArgs = (\(a,b) c -> (a,b,c)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2021" )

    go :: (Mode,Bool,[FilePath]) -> IO ()
    go (Interactive, opt,files) = runFD4 (runInputT defaultSettings (repl files Interactive opt)) >>
                 return ()
    go (Typecheck, opt, files) =
              runOrFail $ mapM_ (typecheckFile opt) files
    go (InteractiveCEK, opt, files) = runFD4 (runInputT defaultSettings (repl files InteractiveCEK opt)) >>
                 return () --Consultar si esto esta bien
    go (Bytecompile, opt, files) =
              runOrFail $ mapM_ (bytecompileFile opt) files
    go (RunVM, _, files) =
              runOrFail $ mapM_ bytecodeRun files
    go (CC, opt, files) =
              runOrFail $ mapM_ (ccFile opt) files
    -- go (Canon,_, files) =
    --           runOrFail $ mapM_ canonFile files 
    -- go (LLVM,_, files) =
    --           runOrFail $ mapM_ llvmFile files
    -- go (Build,_, files) =
    --           runOrFail $ mapM_ buildFile files

runOrFail :: FD4 a -> IO a
runOrFail m = do
  r <- runFD4 m
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v


repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> Mode -> Bool -> InputT m ()
repl args mode opt = do
       lift $ catchErrors $ compileFiles opt args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c mode opt
                       maybe loop (`when` loop) b

compileFiles ::  MonadFD4 m => Bool -> [FilePath] -> m ()
compileFiles _ []       = return ()
compileFiles opt (x:xs) = do
        modify (\s -> s { lfile = x, inter = False })
        compileFile opt x
        compileFiles opt xs

loadFile ::  MonadFD4 m => FilePath -> m [SDecl STerm]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile ::  MonadFD4 m => Bool -> FilePath -> m ()
compileFile opt f = do
    printFD4 ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    decls <- parseIO filename program x
    mapM_ (handleDecl opt) decls

typecheckFile ::  MonadFD4 m => Bool -> FilePath -> m ()
typecheckFile opt f = do
    printFD4  ("Chequeando "++f)
    decls <- loadFile f
    ppterms <- mapM (typecheckDecl opt >=> sppDecl) decls
    mapM_ printFD4 ppterms

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

typecheckDecl :: MonadFD4 m => Bool -> SDecl STerm -> m (Decl Term)
typecheckDecl opt a@(SDeclFun pos _ _ _ _ _) = do
        output <- desugarDecl a
        case output of
          DeclFun i n ty t -> do elabTerm <- elab t
                                 elabTerm' <- optimize (if opt then optIter else 0) elabTerm
                                 let dd = DeclFun i n ty elabTerm'
                                 tcDecl dd
                                 return dd
          _ -> failPosFD4 pos "Error interpretando una declaracion"
typecheckDecl _ (SDeclType i n v) = do tyDesugar <- desugarTy v
                                       let dd = DeclType i n tyDesugar
                                       tcDecl dd
                                       return dd

handleDecl ::  MonadFD4 m => Bool -> SDecl STerm -> m ()
handleDecl opt d = do
        output <- typecheckDecl False d -- Llama a typecheck con optimizaciones apagadas para no optimizar 2 veces
        case output of
          DeclFun p n ty tt -> do te <- eval tt
                                  printFD4Debug te
                                  tt' <- optimize (if opt then optIter else 0) te
                                  printFD4Debug tt'
                                  addDecl (DeclFun p n ty tt')
          _ -> return ()

data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) c))
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> Mode -> Bool -> m Bool
handleCommand cmd mode opt = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines [ name | name <- reverse (nub (map declName glb)) ])
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e mode opt
                          CompileFile f        -> put (s {lfile=f, cantDecl=0}) >> compileFile opt f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile opt) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> Mode -> Bool -> m ()
compilePhrase x mode opt = do dot <- parseIO "<interactive>" declOrTm x
                              case dot of
                                Left d  -> handleDecl opt d  
                                Right t -> case mode of
                                        Interactive -> handleTerm t eval
                                        InteractiveCEK -> handleTerm t evalCEK
                                        _ -> undefined -- para que no me moleste el linter

handleTerm ::  MonadFD4 m => STerm -> (Term -> m Term) -> m ()
handleTerm t f = do
         elabTerm <- elab t
         s <- get
         ty <- tc elabTerm (tyEnv s)
         te <- f elabTerm
         ppte <- pp te
         printFD4 (ppte ++ " : " ++ ppTy ty)
         
printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    t  <- case x' of
           (SV _ f) -> maybe ex id <$> lookupDecl f
           _       -> return ex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "\nTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         tt <- elab t
         s <- get
         ty <- tc tt (tyEnv s)
         printFD4 (ppTy ty)

-- Filtra las declaraciones de tipos
filterSTypes :: MonadFD4 m => Decl Term -> m Bool
filterSTypes DeclFun {} = return True
filterSTypes DeclType {} = return False

-- Para compilar y correr bytecode
bytecompileFile :: MonadFD4 m => Bool -> FilePath -> m ()
bytecompileFile opt fp = do xs <- loadFile fp
                            ys <- mapM (typecheckDecl opt) xs
                            ys' <- filterM filterSTypes ys
                            byte <- bytecompileModule ys'
                            liftIO $ bcWrite byte (replaceExtension fp ".o")
                            return ()


bytecodeRun :: MonadFD4 m => FilePath -> m()
bytecodeRun fp = do file <- liftIO $ bcRead fp
                    runBC file

-- Para compilar en C
typecheckDeclTy :: MonadFD4 m => Bool -> SDecl STerm -> m (Decl TTerm)
typecheckDeclTy opt a@(SDeclFun pos _ _ _ _ _) = do
        output <- desugarDecl a
        case output of
          DeclFun i n ty t -> do elabTerm <- elab t
                                 elabTerm' <- optimize (if opt then optIter else 0) elabTerm
                                 let dd = DeclFun i n ty elabTerm'
                                 dd' <- tcDeclTy dd
                                 return dd'
          _ -> failPosFD4 pos "Error interpretando una declaracion"
typecheckDeclTy _ (SDeclType i n v) = do tyDesugar <- desugarTy v
                                         let dd = DeclType i n tyDesugar
                                         tcDecl dd
                                         return dd

ccFile :: MonadFD4 m => Bool -> FilePath -> m()
ccFile opt fp = do xs <- loadFile fp
                   ys <- mapM (typecheckDeclTy opt) xs
                   let imp = compilaC ys
                   liftIO $ cWrite imp (replaceExtension fp ".c")
                   return ()


-- Para optimizar
optIter :: Int
optIter = 10

optimize :: MonadFD4 m => Int -> Term -> m Term
optimize 0 term = return term
optimize n term = do
  tmm <- optimizer term
  b <- getOptimiz
  if b
    then optimize (n-1) tmm
       else do resetOptimiz
               return tmm