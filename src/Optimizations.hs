{-# LANGUAGE PatternSynonyms #-}

module Optimizations where

import Eval
import Global
import Lang
import MonadFD4
import PPrint
import Subst
import TypeChecker

-- Constant Folding and Propagation
pattern CONST :: Int -> Tm info var
pattern CONST n <- Const _ (CNat n)

changeContstant :: MonadFD4 m => Term -> m Term
changeContstant t = modifyOptimized >> constantOpt t

constantOpt :: MonadFD4 m => Term -> m Term
constantOpt (BinaryOp info bOp (CONST c1) (CONST c2)) = changeContstant $ Const info $ CNat $ semOp bOp c1 c2
constantOpt (BinaryOp _ _ term (CONST 0)) = changeContstant term
constantOpt (BinaryOp _ Add (CONST 0) term) = changeContstant term
constantOpt (IfZ _ (CONST 0) term _) = changeContstant term
constantOpt (IfZ _ (CONST _) _ term) = changeContstant term
constantOpt (Let _ _ _ c@(CONST _) tm) = changeContstant $ subst' c tm
constantOpt t = return t

changeInline :: MonadFD4 m => Term -> m Term
changeInline t = modifyOptimized >> inlineAndDead t

-- Inline Expansion and Dead Code Elimination

inlineAndDead :: MonadFD4 m => Term -> m Term
inlineAndDead t@(Let info name _ tm1 tm2) = do
  let calls = numCall tm2
  let size = termSize tm1
  temporal calls size
  where
    temporal calls size
      | calls == 0 = do
        stm <- spp t
        printFD4 $ "Cuidado: Variable sin usar " ++ name ++ " en el término:\n " ++ stm ++ "\n En línea: " ++ show info
        changeInline tm2
      | calls == 1 = changeInline $ subst' tm1 tm2
      | calls > 10 = changeInline $ subst' tm1 tm2
      | otherwise =
        if size < 10
          then changeInline $ subst' tm1 tm2
          else return t
inlineAndDead a@(App _ t1@(Lam _ _ _ t) t2) =
  case t2 of
    CONST _ -> changeInline $ subst' t2 t
    V _ _ -> changeInline $ subst' t2 t
    _ -> return a
inlineAndDead t = return t

-- Common Subexpresion Elimination
-- changecse :: MonadFD4 m => Term -> m Term
-- changecse t = modifyOptimized >> cse t

notPrint :: Term -> Bool
notPrint (V _ _) = True
notPrint (Const _ _) = True
notPrint (Lam _ _ _ tm) = notPrint tm
notPrint (App _ tm1 tm2) = notPrint tm1 && notPrint tm2
notPrint (Print _ _ tm) = False
notPrint (BinaryOp _ _ tm1 tm2) = notPrint tm1 && notPrint tm2
notPrint (Fix _ _ _ _ _ tm) = notPrint tm
notPrint (IfZ _ tb tt tf) = and [notPrint tb, notPrint tt, notPrint tf]
notPrint (Let _ _ _ tm1 tm2) = notPrint tm1 && notPrint tm2

notBound :: Term -> Bool
notBound (V _ (Bound _)) = False
notBound _ = True

-- cse :: MonadFD4 m => [(Name, Ty)] -> Term -> m Term
-- cse t@(BinaryOp info bOp tm1 tm2) =
--   if (tm1 == tm2 && notPrint tm1 && notBound tm1)
--     then do
--       s <- get
--       (ty, _) <- tcTy tm1 (tyEnv s) []
--       changecse $ Let info "Caca" ty tm1 (BinaryOp info bOp (V info (Bound 0)) (V info (Bound 0)))
--     else return t
-- cse t = return t

numCall :: Term -> Int
numCall tm = numCall' 0 tm

numCall' :: Int -> Term -> Int
numCall' i (V _ v) = case v of
  Bound n -> if i == n then 1 else 0
  _ -> 0
numCall' _ (Const _ _) = 0
numCall' i (Lam _ _ _ tm) = numCall' (i + 1) tm
numCall' i (App _ tm1 tm2) = numCall' i tm1 + numCall' i tm2
numCall' i (Print _ _ tm) = numCall' i tm
numCall' i (BinaryOp _ _ tm1 tm2) = numCall' i tm1 + numCall' i tm2
numCall' i (Fix _ _ _ _ _ tm) = numCall' (i + 2) tm -- Es 2 porque esta el bound a la f y a la x
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
termSize (Let _ _ _ tm1 _) = 1 + termSize tm1 -- Queremos el tamaño del argumento

optimizer :: MonadFD4 m => Term -> m Term
optimizer t =
  return t
    >>= constantOpt
    >>= inlineAndDead
    -- >>= cse
    >>= visitor

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

hasNameTy :: Name -> Ty -> Bool
hasNameTy _ NatTy = False
hasNameTy name (FunTy d c) = hasNameTy name d || hasNameTy name c
hasNameTy name (NameTy nt tt) = name == nt || hasNameTy name tt

hasNameTerm :: Name -> Term -> Bool
hasNameTerm name (V _ (Global str)) = str == name
hasNameTerm name (V _ _) = False
hasNameTerm name (Const _ _) = False
hasNameTerm name (Lam _ _ ty tm) = hasNameTy name ty || hasNameTerm name tm
hasNameTerm name (App _ tm1 tm2) = hasNameTerm name tm1 || hasNameTerm name tm2
hasNameTerm name (Print _ _ tm) = hasNameTerm name tm
hasNameTerm name (BinaryOp _ _ tm1 tm2) = hasNameTerm name tm1 || hasNameTerm name tm2
hasNameTerm name (Fix _ _ ty1 _ ty2 tm) = hasNameTy name ty1 || hasNameTy name ty2 || hasNameTerm name tm
hasNameTerm name (IfZ _ tb tt tf) = hasNameTerm name tb || hasNameTerm name tt || hasNameTerm name tf
hasNameTerm name (Let _ _ ty tm1 tm2) = hasNameTerm name tm1 || hasNameTerm name tm2 || hasNameTy name ty

hasNameDecl :: Name -> Decl Term -> Bool
hasNameDecl name (DeclFun _ _ ty body) = hasNameTy name ty || hasNameTerm name body
hasNameDecl name (DeclType _ _ ty) = hasNameTy name ty

deadCodeEliminationDecl :: MonadFD4 m => [Decl Term] -> m [Decl Term]
deadCodeEliminationDecl [] = return []
deadCodeEliminationDecl a@[_] = return a
deadCodeEliminationDecl (x : xs) =
  let name = declName x
      aparece = or $ map (hasNameDecl name) xs
   in if aparece
        then deadCodeEliminationDecl xs >>= return . (x :) -- Chanchada de Santi
        else modifyOptimized >> deadCodeEliminationDecl xs