module Optimizations where

import Eval
import Lang
import MonadFD4
import Subst

-- Preguntar a Mauro: ¿Hacemos una funcion por optimizacion?
-- Consideramos importante mantener los efectos secundarios
optimizer :: MonadFD4 m => Term -> m Term
-- seccion de constant folding
optimizer (BinaryOp info bOp (Const _ (CNat c1)) (Const _ (CNat c2))) = do
  modifyOptimiz
  return $ Const info $ CNat $ semOp bOp c1 c2

-- constant propagation
optimizer (Let info name ty (Const _ c) tm) = do
  let tm' = varChanger (\_ p n -> V p (Free n)) replaceVar tm
  modifyOptimiz
  optimizer tm'
  where
    replaceVar depth p i
      | i == depth = Const p c
      | i > depth = V p (Bound $ i - 1)
      | otherwise = V p (Bound i)

-- resto
optimizer t@(V _ _) = return t
optimizer t@(Const _ _) = return t
optimizer (Lam info name ty tm) = do
  tmm <- optimizer tm
  return $ Lam info name ty tmm
optimizer (App info tm1 tm2) = do
  tmm1 <- optimizer tm1
  tmm2 <- optimizer tm2
  return $ App info tmm1 tmm2
optimizer (Print info str tm) = do
  tmm <- optimizer tm
  return $ Print info str tmm
optimizer (BinaryOp info bOp tm1 tm2) = do
  tm1' <- optimizer tm1
  tm2' <- optimizer tm2
  return $ BinaryOp info bOp tm1' tm2'
optimizer (Fix info fName fTy vName vTy tm) = do
  tm' <- optimizer tm
  return $ Fix info fName fTy vName vTy tm'
optimizer (IfZ info tmb tmt tmf) = do
  tmb' <- optimizer tmb
  tmt' <- optimizer tmt
  tmf' <- optimizer tmf
  return $ IfZ info tmb' tmt' tmf'
optimizer (Let info name ty tm1 tm2) = do
  tm1' <- optimizer tm1
  tm2' <- optimizer tm2
  return $ Let info name ty tm1' tm2'