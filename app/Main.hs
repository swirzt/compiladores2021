{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Main
-- Description : Compilador de FD4.
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
module Main where

import Bytecompile (bcRead, bcWrite, bytecompileModule, runBC)
import CEK
import ClosureConvert
import Control.Exception (IOException, catch)
import Control.Monad.Catch (MonadMask)
import Data.Char (isSpace)
import Data.List (intersperse, isPrefixOf, nub)
import Elab (desugarDecl, desugarTy, elab)
import Errors
import Eval (eval)
import Global (GlEnv (..), Mode (..))
import Lang
import MonadFD4
import Optimizations
import Options.Applicative
import PPrint
import Parse (P, declOrTm, program, runP, tm)
import System.Console.Haskeline (InputT, defaultSettings, getInputLine, runInputT)
import System.Exit
import System.FilePath.Windows (replaceExtension)
import System.IO (hPrint, hPutStrLn, stderr)
import TypeChecker (tc, tcDecl, tcDeclTy)

prompt :: String
prompt = "FD4> "

-- | Parser de banderas
parseMode :: Parser (Mode, Bool)
parseMode =
  (,)
    <$> ( flag' Typecheck (long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
            <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
            <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
            <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
            <|> flag Interactive Interactive (long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
            <|> flag' CC (long "cc" <> short 'c' <> help "Compilar a código C")
        )
    <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode, Bool, [FilePath])
parseArgs = (\(a, b) c -> (a, b, c)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts =
      info
        (parseArgs <**> helper)
        ( fullDesc
            <> progDesc "Compilador de FD4"
            <> header "Compilador de FD4 de la materia Compiladores 2021"
        )
    go :: (Mode, Bool, [FilePath]) -> IO ()
    go (Interactive, opt, files) =
      runFD4 opt (Just Interactive) (runInputT defaultSettings (repl files))
        >> return ()
    go (Typecheck, opt, files) =
      runOrFail opt $ mapM_ typecheckFile files
    go (InteractiveCEK, opt, files) =
      runFD4 opt (Just InteractiveCEK) (runInputT defaultSettings (repl files))
        >> return ()
    go (Bytecompile, opt, files) =
      runOrFail opt $ mapM_ bytecompileFile files
    go (RunVM, _, files) =
      runOrFail False $ mapM_ bytecodeRun files
    go (CC, opt, files) =
      runOrFail opt $ mapM_ ccFile files

runOrFail :: Bool -> FD4 a -> IO a
runOrFail b m = do
  r <- runFD4 b Nothing m
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
  lift $ catchErrors $ compileFiles args
  s <- lift get
  when (inter s) $
    liftIO $
      putStrLn
        ( "Entorno interactivo para FD4.\n"
            ++ "Escriba :? para recibir ayuda."
        )
  loop
  where
    loop = do
      minput <- getInputLine prompt
      case minput of
        Nothing -> return ()
        Just "" -> loop
        Just x -> do
          c <- liftIO $ interpretCommand x
          b <- lift $ catchErrors $ handleCommand c
          maybe loop (`when` loop) b

compileFiles :: MonadFD4 m => [FilePath] -> m ()
compileFiles [] = return ()
compileFiles (x : xs) = do
  modify (\s -> s {lfile = x, inter = False})
  compileFile x
  compileFiles xs

loadFile :: MonadFD4 m => FilePath -> m [SDecl STerm]
loadFile f = do
  let filename = reverse (dropWhile isSpace (reverse f))
  x <-
    liftIO $
      catch
        (readFile filename)
        ( \e -> do
            let err = show (e :: IOException)
            hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
            return ""
        )
  setLastFile filename
  parseIO filename program x

compileFile :: MonadFD4 m => FilePath -> m ()
compileFile f = do
  printFD4 ("Abriendo " ++ f ++ "...")
  let filename = reverse (dropWhile isSpace (reverse f))
  x <-
    liftIO $
      catch
        (readFile filename)
        ( \e -> do
            let err = show (e :: IOException)
            hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
            return ""
        )
  decls <- parseIO filename program x
  mapM_ handleDecl decls

fmapM :: (MonadFD4 m, Show info, Eq info) => (Tm info var -> m (Tm info var)) -> Decl (Tm info var) -> m (Decl (Tm info var))
fmapM _ d@(DeclType _ _ _) = return d
fmapM f (DeclFun i n t term) = do
  term' <- f term
  return $ DeclFun i n t term'

typecheckFile :: MonadFD4 m => FilePath -> m ()
typecheckFile f = do
  printFD4 ("Chequeando " ++ f)
  decls <- loadFile f
  ldecls <- mapM typecheckDecl decls
  opt <- getOpti
  let declOp =
        if opt
          then optimizeDecls optIter
          else return
  ldecls' <- declOp ldecls
  ppterms <- mapM sppDecl ldecls'
  mapM_ printFD4 ppterms

parseIO :: MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
  Left e -> throwError (ParseErr e)
  Right r -> return r

typecheckDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
typecheckDecl a@(SDeclFun pos _ _ _ _ _) = do
  output <- desugarDecl a
  case output of
    DeclFun i n ty t -> do
      elabTerm <- elab t
      let dd = DeclFun i n ty elabTerm
      tcDecl dd
      return dd
    _ -> failPosFD4 pos "Error interpretando una declaracion"
typecheckDecl (SDeclType i n v) = do
  tyDesugar <- desugarTy v
  let dd = DeclType i n tyDesugar
  tcDecl dd
  return dd

handleDecl :: MonadFD4 m => SDecl STerm -> m ()
handleDecl d = do
  output <- typecheckDecl d
  opt <- getOpti
  let f = if opt then optimize optIter else return
  output' <- fmapM f output
  case output' of
    DeclFun p n ty tt -> do
      te <- eval tt
      addDecl (DeclFun p n ty te)
    a@(DeclType _ _ _) -> addDecl a

data Command
  = Compile CompileForm
  | PPrint String
  | Type String
  | Reload
  | Browse
  | Quit
  | Help
  | Noop

data CompileForm
  = CompileInteractive String
  | CompileFile String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x =
  if ":" `isPrefixOf` x
    then do
      let (cmd, t') = break isSpace x
          t = dropWhile isSpace t'
      --  find matching commands
      let matching = filter (\(Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
      case matching of
        [] -> do
          putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
          return Noop
        [Cmd _ _ f _] ->
          do return (f t)
        _ -> do
          putStrLn
            ( "Comando ambigüo, podría ser "
                ++ concat (intersperse ", " [head cs | Cmd cs _ _ _ <- matching])
                ++ "."
            )
          return Noop
    else return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands =
  [ Cmd [":browse"] "" (const Browse) "Ver los nombres en scope",
    Cmd
      [":load"]
      "<file>"
      (Compile . CompileFile)
      "Cargar un programa desde un archivo",
    Cmd [":print"] "<exp>" PPrint "Imprime un término y sus ASTs sin evaluarlo",
    Cmd [":reload"] "" (const Reload) "Vuelve a cargar el último archivo cargado",
    Cmd [":type"] "<exp>" Type "Chequea el tipo de una expresión",
    Cmd [":quit", ":Q"] "" (const Quit) "Salir del intérprete",
    Cmd [":help", ":?"] "" (const Help) "Mostrar esta lista de comandos"
  ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs =
  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n"
    ++ "c es el primer caracter del nombre completo.\n\n"
    ++ "<expr>                  evaluar la expresión\n"
    ++ "let <var> = <expr>      definir una variable\n"
    ++ unlines
      ( map
          ( \(Cmd c a _ d) ->
              let ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) c))
               in ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d
          )
          cs
      )

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand :: MonadFD4 m => Command -> m Bool
handleCommand cmd = do
  s@GlEnv {..} <- get
  case cmd of
    Quit -> return False
    Noop -> return True
    Help -> printFD4 (helpTxt commands) >> return True
    Browse -> do
      printFD4 (unlines [name | name <- reverse (nub (map declName glb))])
      return True
    Compile c ->
      do
        case c of
          CompileInteractive e -> compilePhrase e
          CompileFile f -> put (s {lfile = f, cantDecl = 0}) >> compileFile f
        return True
    Reload -> eraseLastFileDecls >> getLastFile >>= compileFile >> return True
    PPrint e -> printPhrase e >> return True
    Type e -> typeCheckPhrase e >> return True

compilePhrase :: MonadFD4 m => String -> m ()
compilePhrase x = do
  dot <- parseIO "<interactive>" declOrTm x
  case dot of
    Left d -> handleDecl d
    Right t -> do
      mode <- getMode
      case mode of
        Just Interactive -> handleTerm t eval
        Just InteractiveCEK -> handleTerm t evalCEK
        _ -> failFD4 "Se quizo hacer interactive sin un modo"

handleTerm :: MonadFD4 m => STerm -> (Term -> m Term) -> m ()
handleTerm t f = do
  elabTerm <- elab t
  s <- get
  ty <- tc elabTerm (tyEnv s)
  te <- f elabTerm
  ppte <- pp te
  printFD4 (ppte ++ " : " ++ ppTy ty)

printPhrase :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    t <- case x' of
      (SV _ f) -> maybe ex id <$> lookupDecl f
      _ -> return ex
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
bytecompileFile :: MonadFD4 m => FilePath -> m ()
bytecompileFile fp = do
  xs <- loadFile fp
  ys <- mapM typecheckDecl xs
  ys' <- filterM filterSTypes ys
  opt <- getOpti
  let f = if opt then optimizeDecls optIter else return
  zs <- f ys'
  byte <- bytecompileModule zs
  liftIO $ bcWrite byte (replaceExtension fp ".o")
  return ()

bytecodeRun :: MonadFD4 m => FilePath -> m ()
bytecodeRun fp = do
  file <- liftIO $ bcRead fp
  printFD4Debug file
  runBC file

-- Para compilar en C
typecheckDeclTy :: MonadFD4 m => SDecl STerm -> m (Decl TTerm)
typecheckDeclTy a@(SDeclFun pos _ _ _ _ _) = do
  output <- desugarDecl a
  case output of
    DeclFun i n ty t -> do
      elabTerm <- elab t
      let dd = DeclFun i n ty elabTerm
      dd' <- tcDeclTy dd
      return dd'
    _ -> failPosFD4 pos "Error interpretando una declaracion"
typecheckDeclTy (SDeclType i n v) = do
  tyDesugar <- desugarTy v
  let dd = DeclType i n tyDesugar
  tcDecl dd
  return dd

ccFile :: MonadFD4 m => FilePath -> m ()
ccFile fp = do
  xs <- loadFile fp
  ys <- mapM typecheckDeclTy xs
  opt <- getOpti
  let f = if opt then optimize optIter else return
  ys' <- mapM (fmapM f) ys
  -- printFD4Debug ys'
  let imp = compilaC ys'
  liftIO $ cWrite imp (replaceExtension fp ".c")
  return ()

-- Para optimizar
optIter :: Int
optIter = 100

optimize :: (MonadFD4 m, Show info, Eq info) => Int -> Tm info Var -> m (Tm info Var)
optimize 0 term = return term
optimize n term = do
  tmm <- optimizer term
  b <- getOptimized
  resetOptimized
  if b
    then optimize (n - 1) tmm
    else return tmm

optimizeDecls :: MonadFD4 m => Int -> [Decl Term] -> m [Decl Term]
optimizeDecls 0 xs = return xs
optimizeDecls n xs = do
  ys <- optimizerDecl xs >>= mapM (fmapM optimizer)
  b <- getOptimized
  resetOptimized
  if b
    then optimizeDecls (n - 1) ys
    else return ys