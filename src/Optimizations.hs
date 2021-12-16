{-# LANGUAGE PatternSynonyms #-}

module Optimizations where

import Eval
import Lang
import MonadFD4
import Subst

-- Constant Folding and Propagation
pattern CONST :: Int -> Tm info var
pattern CONST n <- Const _ (CNat n)

changeContstant :: (MonadFD4 m, Show info, Eq info) => Tm info Var -> m (Tm info Var)
changeContstant t = modifyOptimized >> constantOpt t

constantOpt :: (MonadFD4 m, Show info, Eq info) => (Tm info Var) -> m (Tm info Var)
constantOpt (BinaryOp info bOp (CONST c1) (CONST c2)) = changeContstant $ Const info $ CNat $ semOp bOp c1 c2
constantOpt (BinaryOp _ _ term (CONST 0)) = changeContstant term
constantOpt (BinaryOp _ Add (CONST 0) term) = changeContstant term
constantOpt (IfZ _ (CONST 0) term _) = changeContstant term
constantOpt (IfZ _ (CONST _) _ term) = changeContstant term
constantOpt (IfZ i b (IfZ _ b' algo nada1) nada2) | nada1 == nada2 = changeContstant $ IfZ i (BinaryOp i Add b b') algo nada1
constantOpt (Let _ _ _ c@(CONST _) tm) = changeContstant $ subst' c tm
constantOpt t = return t

changeInline :: (MonadFD4 m, Show info, Eq info) => (Tm info Var) -> m (Tm info Var)
changeInline t = modifyOptimized >> inlineAndDead t

-- Inline Expansion and Dead Code Elimination
pattern BOUND :: Int -> Tm info Var
pattern BOUND i <- V _ (Bound i)

inlineAndDead :: (MonadFD4 m, Show info, Eq info) => (Tm info Var) -> m (Tm info Var)
inlineAndDead t@(Let _ _ _ _ (BinaryOp _ _ (BOUND _) (BOUND _))) = return t -- No expandimos porque viene de cse
inlineAndDead t@(Let _ name _ tm1 tm2) = do
  let calls = numCall tm2
  let size = termSize tm1
  temporal calls size
  where
    temporal calls size
      | calls == 0 = do
        printFD4 $ "Cuidado: Definición de let sin usar: " ++ name
        changeInline (subBound tm2)
      | calls == 1 = changeInline $ subst' tm1 tm2
      | calls > 10 = changeInline $ subst' tm1 tm2
      | otherwise =
        if size < 10
          then changeInline $ subst' tm1 tm2
          else return t
inlineAndDead a@(App _ (Lam _ _ _ t) t2) =
  case t2 of
    CONST _ -> changeInline $ subst' t2 t
    V _ _ -> changeInline $ subst' t2 t
    _ -> return a
inlineAndDead t = return t

-- Common Subexpresion Elimination

changecse :: (MonadFD4 m, Show info, Eq info) => (Tm info Var) -> m (Tm info Var)
changecse t = modifyOptimized >> return t

notPrint :: (Tm info Var) -> Bool
notPrint (V _ _) = True
notPrint (Const _ _) = True
notPrint (Lam _ _ _ tm) = notPrint tm
notPrint (App _ tm1 tm2) = notPrint tm1 && notPrint tm2
notPrint (Print _ _ _) = False
notPrint (BinaryOp _ _ tm1 tm2) = notPrint tm1 && notPrint tm2
notPrint (Fix _ _ _ _ _ tm) = notPrint tm
notPrint (IfZ _ tb tt tf) = and [notPrint tb, notPrint tt, notPrint tf]
notPrint (Let _ _ _ tm1 tm2) = notPrint tm1 && notPrint tm2

notBound :: (Tm info Var) -> Bool
notBound (V _ (Bound _)) = False
notBound _ = True

cse :: (MonadFD4 m, Show info, Eq info) => (Tm info Var) -> m (Tm info Var)
cse (BinaryOp info bOp tm1 tm2) | notBound tm1 && tm1 == tm2 && notPrint tm1 = do
  var <- getFresh
  let varname = "cse_" ++ show var
  changecse $ Let info varname NatTy tm1 (BinaryOp info bOp (V info (Bound 0)) (V info (Bound 0)))
cse t = return t

numCall :: (Tm info Var) -> Int
numCall tm = numCall' 0 tm

numCall' :: Int -> (Tm info Var) -> Int
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

termSize :: (Tm info Var) -> Int
termSize (V _ _) = 1 -- ¿Que pasa si es una variable global?
termSize (Const _ _) = 1
termSize (Lam _ _ _ tm) = 1 + termSize tm
termSize (App _ tm1 tm2) = 1 + max (termSize tm1) (termSize tm2)
termSize (Print _ _ tm) = 1 + termSize tm
termSize (BinaryOp _ _ tm1 tm2) = 1 + max (termSize tm1) (termSize tm2)
termSize (Fix _ _ _ _ _ tm) = 1 + termSize tm
termSize (IfZ _ tb tt tf) = 1 + maximum [(termSize tb), (termSize tt), (termSize tf)]
termSize (Let _ _ _ tm1 _) = 1 + termSize tm1 -- Queremos el tamaño del argumento

optimizer :: (MonadFD4 m, Show info, Eq info) => (Tm info Var) -> m (Tm info Var)
optimizer =
  constantOpt
    >=> inlineAndDead
    >=> cse
    >=> visitor optimizer

visitor :: (MonadFD4 m, Show info, Eq info) => ((Tm info Var) -> m (Tm info Var)) -> (Tm info Var) -> m (Tm info Var)
visitor _ t@(V _ _) = return t
visitor _ t@(Const _ _) = return t
visitor f (Lam info name ty tm) = do
  tmm <- f tm
  return $ Lam info name ty tmm
visitor f (App info tm1 tm2) = do
  tmm1 <- f tm1
  tmm2 <- f tm2
  return $ App info tmm1 tmm2
visitor f (Print info str tm) = do
  tmm <- f tm
  return $ Print info str tmm
visitor f (BinaryOp info bOp tm1 tm2) = do
  tm1' <- f tm1
  tm2' <- f tm2
  return $ BinaryOp info bOp tm1' tm2'
visitor f (Fix info fName fTy vName vTy tm) = do
  tm' <- f tm
  return $ Fix info fName fTy vName vTy tm'
visitor f (IfZ info tmb tmt tmf) = do
  tmb' <- f tmb
  tmt' <- f tmt
  tmf' <- f tmf
  return $ IfZ info tmb' tmt' tmf'
visitor f (Let info name ty tm1 tm2) = do
  tm1' <- f tm1
  tm2' <- f tm2
  return $ Let info name ty tm1' tm2'

hasNameTy :: Name -> Ty -> Bool
hasNameTy _ NatTy = False
hasNameTy name (FunTy d c) = hasNameTy name d || hasNameTy name c
hasNameTy name (NameTy nt tt) = name == nt || hasNameTy name tt

hasNameTerm :: Name -> Term -> Bool
hasNameTerm name (V _ (Global str)) = str == name
hasNameTerm _ (V _ _) = False
hasNameTerm _ (Const _ _) = False
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

replaceGlobal :: Name -> Term -> Term -> Term
replaceGlobal name tm (V _ (Global name')) | name == name' = tm
replaceGlobal _ _ v@(V _ _) = v
replaceGlobal _ _ c@(Const _ _) = c
replaceGlobal name tm (Lam info nn ty tmm) = Lam info nn ty $ replaceGlobal name tm tmm
replaceGlobal name tm (App info tm1 tm2) = App info (replaceGlobal name tm tm1) (replaceGlobal name tm tm2)
replaceGlobal name tm (Print info str tm') = Print info str $ replaceGlobal name tm tm'
replaceGlobal name tm (BinaryOp info bOp tm1 tm2) = BinaryOp info bOp (replaceGlobal name tm tm1) (replaceGlobal name tm tm2)
replaceGlobal name tm (Fix info fname ty1 vname ty2 tm') = Fix info fname ty1 vname ty2 $ replaceGlobal name tm tm'
replaceGlobal name tm (IfZ i tb tt tf) = IfZ i (replaceGlobal name tm tb) (replaceGlobal name tm tt) (replaceGlobal name tm tf)
replaceGlobal name tm (Let i nn ty tm1 tm2) = Let i nn ty (replaceGlobal name tm tm1) (replaceGlobal name tm tm2)

changeGlobalName :: Name -> Term -> Decl Term -> Decl Term
changeGlobalName name tm = fmap (replaceGlobal name tm)

constantPropagationDecl :: MonadFD4 m => [Decl Term] -> m [Decl Term]
constantPropagationDecl [] = return []
constantPropagationDecl (d@(DeclFun _ name _ t@(CONST _)) : xs) =
  let xs' = map (changeGlobalName name t) xs
   in modifyOptimized >> constantPropagationDecl xs' >>= return . (d :) -- Chanchada de Santi
constantPropagationDecl (d : xs) = constantPropagationDecl xs >>= return . (d :) -- Chanchada de Santi

optimizerDecl :: MonadFD4 m => [Decl Term] -> m [Decl Term]
optimizerDecl = constantPropagationDecl >=> deadCodeEliminationDecl
