module ClosureConvert where

import C
import Control.Monad.Writer
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
  itm <- closureConvert tm
  fname <- generateName "g"
  let fvars = freeVars tm
  tell [IrFun fname fvars itm]
  return $ MkClosure fname (fmap IrVar fvars)
closureConvert (Let _ name _ tn tm) = do
  itn <- closureConvert tn
  itm <- closureConvert tm
  return $ IrLet name itn itm

runCC :: [Decl Term] -> [IrDecl]
runCC t = snd $ runWriter $ runStateT (mapM_ (\d -> fmap closureConvert d) t) 0
  where
    cvt2Closure = do closureConvert d