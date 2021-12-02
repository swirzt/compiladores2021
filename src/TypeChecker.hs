-- |
-- Module      : Typechecker
-- Description : Chequeo de tipos de términos y declaraciones.
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
module TypeChecker
  ( tc,
    tcDecl,
    tcTy,
    tcDeclTy,
    domCod,
  )
where

import Global
import Lang
import MonadFD4
import PPrint
import Subst

-- | 'tc' chequea y devuelve el tipo de un término
-- Si el término no está bien tipado, lanza un error
-- usando la interfaz de las mónadas @MonadFD4@.
tc ::
  MonadFD4 m =>
  -- | término a chequear
  Term ->
  -- | entorno de tipado
  [(Name, Ty)] ->
  -- | tipo del término
  m Ty
tc (V p (Bound _)) _ = failPosFD4 p "typecheck: No deberia haber variables Bound"
tc (V p (Free n)) bs = case lookup n bs of
  Nothing -> failPosFD4 p $ "Variable no declarada " ++ ppName n
  Just ty -> return ty
tc (V p (Global n)) bs = case lookup n bs of
  Nothing -> failPosFD4 p $ "Variable no declarada " ++ ppName n
  Just ty -> return ty
tc (Const _ (CNat _)) _ = return NatTy
tc (Print _ _ t) bs = do
  ty <- tc t bs
  expect NatTy ty t
tc (IfZ _ c t t') bs = do
  tyc <- tc c bs
  expect NatTy tyc c
  tyt <- tc t bs
  tyt' <- tc t' bs
  expect tyt tyt' t'
tc (Lam _ v ty t) bs = do
  ty' <- tc (open v t) ((v, ty) : bs)
  return (FunTy ty ty')
tc (App _ t u) bs = do
  tyt <- tc t bs
  (domm, codd) <- domCod t tyt
  tyu <- tc u bs
  expect domm tyu u
  return codd
tc (Fix p f fty x xty t) bs = do
  (domm, codd) <- domCod (V p (Free f)) fty
  when (domm /= xty) $ do
    failPosFD4
      p
      "El tipo del argumento de un fixpoint debe coincidir con el \
      \dominio del tipo de la función"
  let t' = openN [f, x] t
  ty' <- tc t' ((x, xty) : (f, fty) : bs)
  expect codd ty' t'
  return fty
tc (Let _ v ty def t) bs = do
  ty' <- tc def bs
  expect ty ty' def
  tc (open v t) ((v, ty) : bs)
tc (BinaryOp _ _ t u) bs = do
  tty <- tc t bs
  expect NatTy tty t
  uty <- tc t bs
  expect NatTy uty u

-- | @'typeError' t s@ lanza un error de tipo para el término @t@
typeError ::
  MonadFD4 m =>
  -- | término que se está chequeando
  Term ->
  -- | mensaje de error
  String ->
  m a
typeError t s = do
  ppt <- pp t
  failPosFD4 (getInfo t) $ "Error de tipo en " ++ ppt ++ "\n" ++ s

-- | 'expect' chequea que el tipo esperado sea igual al que se obtuvo
-- y lanza un error si no lo es.
expect ::
  MonadFD4 m =>
  -- | tipo esperado
  Ty ->
  -- | tipo que se obtuvo
  Ty ->
  -- | término que se está chequeando
  Term ->
  m Ty
expect ty ty' t =
  if ty == ty'
    then return ty
    else
      typeError t $
        "Tipo esperado: " ++ ppTy ty
          ++ "\npero se obtuvo: "
          ++ ppTy ty'

-- | 'domCod chequea que un tipo sea función
-- | devuelve un par con el tipo del dominio y el codominio de la función
domCod :: MonadFD4 m => Term -> Ty -> m (Ty, Ty)
domCod _ (FunTy d c) = return (d, c)
domCod t (NameTy _ ty) = domCod t ty
domCod t ty = typeError t $ "Se esperaba un tipo función, pero se obtuvo: " ++ ppTy ty

-- | 'tcDecl' chequea el tipo de una declaración
-- y la agrega al entorno de tipado de declaraciones globales
tcDecl :: MonadFD4 m => Decl Term -> m ()
tcDecl (DeclFun p n t def) = do
  --chequear si el nombre ya está declarado
  mty <- lookupTy n
  case mty of
    Nothing -> do
      --no está declarado
      s <- get
      ty <- tc def (tyEnv s)
      expect t ty def -- Agregado por nosotros, espera el type de la decl
      addTy n ty
    Just _ -> failPosFD4 p $ n ++ " ya está declarado"
tcDecl (DeclType p n t) = do
  mty <- lookupTyDef n
  case mty of
    Nothing -> addTyDef n t
    Just _ -> failPosFD4 p $ n ++ " ya está declarado"

--Funciones para compilar a C

--Funciona como tc pero tambien devuelve el termino como TTerm
tcTy ::
  MonadFD4 m =>
  -- | término a chequear
  Term ->
  -- | entorno de tipado
  [(Name, Ty)] ->
  -- | tipos de los Bound
  [Ty] ->
  -- | tipo del término y término transformado
  m (Ty, TTerm)
tcTy (V _ var@(Bound k)) _ ts = let ty = ts !! k in return $ (ty, V ty var)
tcTy (V p var@(Free n)) bs _ = case lookup n bs of
  Nothing -> failPosFD4 p $ "Variable no declarada " ++ ppName n
  Just ty -> return (ty, V ty var)
tcTy (V p var@(Global n)) bs _ = case lookup n bs of
  Nothing -> failPosFD4 p $ "Variable no declarada " ++ ppName n
  Just ty -> return (ty, V ty var)
tcTy (Const _ k@(CNat _)) _ _ = return (NatTy, Const NatTy k)
tcTy (Print _ str t) bs ts = do
  (ty, t') <- tcTy t bs ts
  expect NatTy ty t
  return (ty, Print ty str t')
tcTy (IfZ _ c t t') bs ts = do
  (tyc, ttmC) <- tcTy c bs ts
  expect NatTy tyc c
  (tyt, ttmT) <- tcTy t bs ts
  (tyt', ttmT') <- tcTy t' bs ts
  expect tyt tyt' t'
  return (tyt, IfZ tyt ttmC ttmT ttmT')
tcTy (Lam _ v ty t) bs ts = do
  (ty', t') <- tcTy t bs (ty : ts)
  let newTy = FunTy ty ty'
  return (newTy, Lam newTy v ty t')
tcTy (App _ t u) bs ts = do
  (tyt, t') <- tcTy t bs ts
  (domm, codd) <- domCod t tyt
  (tyu, u') <- tcTy u bs ts
  expect domm tyu u
  return (codd, App tyt t' u')
tcTy (Fix p f fty x xty t) bs ts = do
  (domm, codd) <- domCod (V p (Free f)) fty
  when (domm /= xty) $ do
    failPosFD4
      p
      "El tipo del argumento de un fixpoint debe coincidir con el \
      \dominio del tipo de la función"
  (ty', t') <- tcTy t bs (xty : fty : ts)
  expect codd ty' t
  return (fty, Fix fty f fty x xty t')
tcTy (Let _ v ty def t) bs ts = do
  (ty', t') <- tcTy def bs ts
  expect ty ty' def
  (ty'', t'') <- tcTy t bs (ty : ts)
  return $ (ty'', Let ty'' v ty t' t'')
tcTy (BinaryOp _ op t u) bs ts = do
  (tty, t') <- tcTy t bs ts
  expect NatTy tty t
  (uty, u') <- tcTy u bs ts
  expect NatTy uty u
  return $ (NatTy, BinaryOp NatTy op t' u')

changeCod :: Ty -> Ty -> Ty
changeCod (FunTy d _) t = FunTy d t
changeCod _ _ = undefined

changeTy :: TTerm -> Ty -> TTerm
changeTy (V _ var) t = V t var
changeTy (Const _ c) t = Const t c
changeTy (Lam _ n ty tm) t = Lam t n ty tm
changeTy (App ty tm1 tm2) t = let nT = changeCod ty t in App nT tm1 tm2
changeTy (Print _ str tm) t = Print t str tm
changeTy (BinaryOp _ bop tm1 tm2) t = BinaryOp t bop tm1 tm2
changeTy (Fix _ f fTy var varTy tm) t = Fix t f fTy var varTy tm
changeTy (IfZ _ tmb tmt tmf) t = IfZ t tmb tmt tmf
changeTy (Let _ name ty tm tm') t = Let t name ty tm tm'

tcDeclTy :: MonadFD4 m => Decl Term -> m (Decl TTerm)
tcDeclTy (DeclFun p n t def) = do
  --chequear si el nombre ya está declarado
  mty <- lookupTy n
  case mty of
    Nothing -> do
      --no está declarado
      s <- get
      (ty, def') <- tcTy def (tyEnv s) []
      expect t ty def -- Agregado por nosotros, espera el type de la decl
      addTy n ty
      let deff = changeTy def' t
      return $ DeclFun p n t deff
    Just _ -> failPosFD4 p $ n ++ " ya está declarado"
tcDeclTy _ = undefined