{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      : MonadFD4
-- Description : Mónada con soporte para estado, errores, e IO.
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
--
-- Definimos la clase de mónadas 'MonadFD4' que abstrae las mónadas con soporte para estado, errores e IO,
-- y la mónada 'FD4' que provee una instancia de esta clase.
module MonadFD4
  ( FD4,
    runFD4,
    lookupDecl,
    lookupTy,
    lookupTyDef,
    printFD4,
    printFD4Char,
    printFD4Debug,
    setLastFile,
    getLastFile,
    eraseLastFileDecls,
    failPosFD4,
    failFD4,
    addDecl,
    addTy,
    addTyDef,
    catchErrors,
    getOptimiz,
    modifyOptimiz,
    resetOptimiz,
    MonadFD4,
    module Control.Monad.Except,
    module Control.Monad.State,
  )
where

import Common
import Control.Monad.Except
import Control.Monad.State
import Data.List (deleteFirstsBy)
import Errors (Error (..))
import Global
import Lang
import System.IO

-- * La clase 'MonadFD4m'

-- | La clase de mónadas 'MonadFD4' clasifica a las mónadas con soporte para operaciones @IO@, estado de tipo 'Global.GlEnv', y errores de tipo 'Errors.Error'.
--
-- Las mónadas @m@ de esta clase cuentan con las operaciones:
--   - @get :: m GlEnv@
--   - @put :: GlEnv -> m ()@
--   - @throwError :: Error -> m a@
--   - @catchError :: m a -> (Error -> m a) -> m a@
--   - @liftIO :: IO a -> m a@
--
-- y otras operaciones derivadas de ellas, como por ejemplo
--   - @modify :: (GlEnv -> GlEnv) -> m ()
class (MonadIO m, MonadState GlEnv m, MonadError Error m) => MonadFD4 m

printFD4 :: MonadFD4 m => String -> m ()
printFD4 = liftIO . putStrLn

printFD4Debug :: (MonadFD4 m, Show a) => a -> m ()
printFD4Debug s = liftIO (print s)

setLastFile :: MonadFD4 m => FilePath -> m ()
setLastFile filename = modify (\s -> s {lfile = filename})

getLastFile :: MonadFD4 m => m FilePath
getLastFile = gets lfile

addDecl :: MonadFD4 m => Decl Term -> m ()
addDecl d = modify (\s -> s {glb = d : glb s, cantDecl = cantDecl s + 1})

addTy :: MonadFD4 m => Name -> Ty -> m ()
addTy n ty = modify (\s -> s {tyEnv = (n, ty) : tyEnv s})

addTyDef :: MonadFD4 m => Name -> Ty -> m ()
addTyDef n ty = modify (\s -> s {typeDefs = (n, ty) : typeDefs s}) --Haskell me da miedo

eraseLastFileDecls :: MonadFD4 m => m ()
eraseLastFileDecls = do
  s <- get
  let n = cantDecl s
      (era, remaining) = splitAt n (glb s)
      tyEnv' = deleteTy (map declName era) (tyEnv s)
  modify (\st -> st {glb = remaining, cantDecl = 0, tyEnv = tyEnv'})
  where
    deleteTy xs ps = deleteFirstsBy (\x y -> fst x == fst y) ps (map (flip (,) NatTy) xs)

hasName :: Name -> Decl a -> Bool
hasName nm (DeclFun {declName = nm'}) = nm == nm'
hasName nm (DeclType _ nm' _) = nm == nm'

lookupDecl :: MonadFD4 m => Name -> m (Maybe Term)
lookupDecl nm = do
  s <- get
  ret (filter (hasName nm) (glb s))
  where
    ret xs = case xs of
      (DeclFun {declBody = e}) : _ -> return (Just e)
      (DeclType _ _ _) : ys -> ret ys
      [] -> return Nothing

lookupTy :: MonadFD4 m => Name -> m (Maybe Ty)
lookupTy nm = do
  s <- get
  return $ lookup nm (tyEnv s)

lookupTyDef :: MonadFD4 m => Name -> m (Maybe Ty)
lookupTyDef nm = do
  s <- get
  return $ lookup nm (typeDefs s)

failPosFD4 :: MonadFD4 m => Pos -> String -> m a
failPosFD4 p s = throwError (ErrPos p s)

failFD4 :: MonadFD4 m => String -> m a
failFD4 = failPosFD4 NoPos

catchErrors :: MonadFD4 m => m a -> m (Maybe a)
catchErrors c =
  catchError
    (Just <$> c)
    ( \e ->
        liftIO $
          hPutStrLn stderr (show e)
            >> return Nothing
    )

printFD4Char :: MonadFD4 m => Char -> m ()
printFD4Char = liftIO . putChar

getOptimiz :: MonadFD4 m => m Bool
getOptimiz = do
  s <- get
  return $ optimiz s

resetOptimiz :: MonadFD4 m => m ()
resetOptimiz = modify (\s -> s {optimiz = False})

modifyOptimiz :: MonadFD4 m => m ()
modifyOptimiz = modify (\s -> s {optimiz = True})

----
-- Importante, no eta-expandir porque GHC no hace una
-- eta-contracción de sinónimos de tipos
-- y Main no va a compilar al escribir `InputT FD4()`

-- | El tipo @FD4@ es un sinónimo de tipo para una mónada construida usando dos transformadores de mónada sobre la mónada @IO@.
-- El transformador de mónad @ExcepT Error@ agrega a la mónada IO la posibilidad de manejar errores de tipo 'Errors.Error'.
-- El transformador de mónadas @StateT GlEnv@ agrega la mónada @ExcepT Error IO@ la posibilidad de manejar un estado de tipo 'Global.GlEnv'.
type FD4 = StateT GlEnv (ExceptT Error IO)

-- | Esta es una instancia vacía, ya que 'MonadFD4' no tiene funciones miembro.
instance MonadFD4 FD4

-- 'runFD4\'' corre una computación de la mónad 'FD4' en el estado inicial 'Global.initialEnv'
runFD4' :: FD4 a -> IO (Either Error (a, GlEnv))
runFD4' c = runExceptT $ runStateT c initialEnv

runFD4 :: FD4 a -> IO (Either Error a)
runFD4 c = fmap fst <$> runFD4' c
