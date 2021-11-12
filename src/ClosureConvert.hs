module ClosureConvert where

import C
import Control.Monad.Writer
import qualified Data.ByteString.Lazy as BS
import GHC.IO.Encoding (BufferCodec (close))
import IR
import Lang
import MonadFD4
import Subst

--Como en freshen pero para obtener un nombre nuevo
--Aumento el contador cuando saco uno
generateName :: Name -> StateT Int (Writer [IrDecl]) Name
generateName n = do
  k <- get
  modify (+ 1)
  return $ "__" ++ n ++ show k

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ var) = case var of
  Free name -> return $ IrVar name
  Global name -> return $ IrGlobal name
  Bound n -> undefined
closureConvert (Const _ var) = return $ IrConst var
closureConvert (Lam _ name _ tm) = do
  let fvars = freeVars tm
  let ttm = open name tm
  itm <- closureConvert ttm
  fname <- generateName "f"
  tell [IrFun fname fvars itm]
  return $ MkClosure fname (fmap IrVar $ name : fvars)
closureConvert (App _ tm1 tm2) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  return $ IrCall (IrAccess itm1 0) [itm1, itm2]
closureConvert (Print _ str tm) = do
  itm <- closureConvert tm
  return $ IrPrint str itm
closureConvert (BinaryOp _ bop tm1 tm2) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  return $ IrBinaryOp bop itm1 itm2
closureConvert (IfZ _ tb tt tf) = do
  tb' <- closureConvert tb
  tt' <- closureConvert tt
  tf' <- closureConvert tf
  return $ IrIfZ tb' tt' tf'
closureConvert (Fix _ fn _ vn _ tm) = do
  let fvars = freeVars tm
  let ttm = openN [vn, fn] tm
  itm <- closureConvert ttm
  fname <- generateName "f"
  tell [IrFun fname fvars itm]
  return $ MkClosure fname (fmap IrVar $ fn : vn : fvars)
closureConvert (Let _ name _ tn tm) = do
  let ttm = open name tm
  itn <- closureConvert tn
  itm <- closureConvert ttm
  return $ IrLet name itn itm

runCC :: [Decl Term] -> [IrDecl]
runCC [] = []
runCC (decl : xs) = case decl of
  DeclType _ _ _ -> runCC xs
  DeclFun _ name ty tt ->
    let ((x, _), xx) = runWriter $ runStateT (closureConvert tt) 0
        y = runCC xs
     in xx ++ y

compilaC :: [Decl Term] -> String
compilaC xs = ir2C $ IrDecls $ runCC xs

cWrite :: String -> FilePath -> IO ()
cWrite cp filename = writeFile filename cp