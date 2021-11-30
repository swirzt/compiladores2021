module Optimizations where

import Eval
import Lang
import MonadFD4
import PPrint
import Subst

-- Constant Folding and Propagation
constantOpt :: MonadFD4 m => Term -> m Term
constantOpt (BinaryOp info bOp (Const _ (CNat c1)) (Const _ (CNat c2))) = do
  modifyOptimiz
  return $ Const info $ CNat $ semOp bOp c1 c2
constantOpt (BinaryOp _ _ term (Const _ (CNat 0))) = do
  modifyOptimiz
  constantOpt term
constantOpt (BinaryOp _ Add (Const _ (CNat 0)) term) = do
  modifyOptimiz
  constantOpt term
constantOpt (IfZ _ (Const _ (CNat 0)) term _) = do
  modifyOptimiz
  constantOpt term
constantOpt (IfZ _ (Const _ (CNat _)) _ term) = do
  modifyOptimiz
  constantOpt term
constantOpt (Let _ _ _ c@(Const _ _) tm) = do
  modifyOptimiz
  constantOpt $ subst c tm
constantOpt t = return t

inlineAndDead :: MonadFD4 m => Term -> m Term
inlineAndDead t@(Let info name ty tm1 tm2) = do
  let calls = numCall tm2
  let size = termSize tm1
  temporal calls size
  where
    temporal calls size
      | calls == 0 = do
        modifyOptimiz
        stm <- spp t
        printFD4 $ "Cuidado: Variable sin usar " ++ name ++ " en el término:\n " ++ stm ++ "\n En línea: " ++ show info
        inlineAndDead tm2
      | calls == 1 = do
        modifyOptimiz
        inlineAndDead $ subst tm1 tm2
      | calls > 10 = do
        modifyOptimiz
        inlineAndDead $ subst tm1 tm2
      | otherwise =
        if size < 10
          then do
            modifyOptimiz
            inlineAndDead $ subst tm1 tm2
          else do
            tm1' <- inlineAndDead tm1
            tm2' <- inlineAndDead tm2
            return $ Let info name ty tm1' tm2'
inlineAndDead t = return t

numCall :: Term -> Int
numCall tm = numCall' 0 tm

numCall' :: Int -> Term -> Int
numCall' i (V _ v) = case v of
  Bound n -> if i == n then 1 else 0
  _ -> 0
numCall' i (Const _ _) = 0
numCall' i (Lam _ _ _ tm) = numCall' (i + 1) tm
numCall' i (App _ tm1 tm2) = numCall' i tm1 + numCall' i tm2
numCall' i (Print _ _ tm) = numCall' i tm
numCall' i (BinaryOp _ _ tm1 tm2) = numCall' i tm1 + numCall' i tm2
numCall' i (Fix _ _ _ _ _ tm) = numCall' (i + 1) tm
numCall' i (IfZ _ tm1 tm2 tm3) = numCall' i tm1 + numCall' i tm2 + numCall' i tm3
numCall' i (Let _ _ _ tm1 tm2) = numCall' i tm1 + numCall' (i + 1) tm2

termSize :: Term -> Int
termSize (V _ _) = 1 -- ¿Que pasa si es una variable global?
termSize (Const _ _) = 1
termSize (Lam _ _ _ tm) = 1 + termSize tm
termSize (App _ tm1 tm2) = 1 + max (termSize tm1) (termSize tm2)
termSize (Print _ _ tm) = 1 + termSize tm
termSize (BinaryOp _ _ tm1 tm2) = 1 + max (termSize tm1) (termSize tm2)
termSize (Fix _ _ _ _ _ tm) = 1 + termSize tm
termSize (IfZ _ tb tt tf) = 1 + maximum [(termSize tb), (termSize tt), (termSize tf)]
termSize (Let _ _ _ tm1 _) = 1 + termSize tm1 -- Queremos el tamano del argumento

optimizer :: MonadFD4 m => Term -> m Term
optimizer t = constantOpt t >>= inlineAndDead >>= visitor

visitor :: MonadFD4 m => Term -> m Term
visitor t@(V _ _) = return t
visitor t@(Const _ _) = return t
visitor (Lam info name ty tm) = do
  tmm <- optimizer tm
  return $ Lam info name ty tmm
visitor (App info tm1 tm2) = do
  tmm1 <- optimizer tm1
  tmm2 <- optimizer tm2
  return $ App info tmm1 tmm2
visitor (Print info str tm) = do
  tmm <- optimizer tm
  return $ Print info str tmm
visitor (BinaryOp info bOp tm1 tm2) = do
  tm1' <- optimizer tm1
  tm2' <- optimizer tm2
  return $ BinaryOp info bOp tm1' tm2'
visitor (Fix info fName fTy vName vTy tm) = do
  tm' <- optimizer tm
  return $ Fix info fName fTy vName vTy tm'
visitor (IfZ info tmb tmt tmf) = do
  tmb' <- optimizer tmb
  tmt' <- optimizer tmt
  tmf' <- optimizer tmf
  return $ IfZ info tmb' tmt' tmf'
visitor (Let info name ty tm1 tm2) = do
  tm1' <- optimizer tm1
  tm2' <- optimizer tm2
  return $ Let info name ty tm1' tm2'