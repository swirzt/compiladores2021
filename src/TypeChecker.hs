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
tcTy (V _ var@(Bound k)) _ ts = let ty = ts !! k in return $ (ty, TV var ty)
tcTy (V p var@(Free n)) bs _ = case lookup n bs of
  Nothing -> failPosFD4 p $ "Variable no declarada " ++ ppName n
  Just ty -> return (ty, TV var ty)
tcTy (V p var@(Global n)) bs _ = case lookup n bs of
  Nothing -> failPosFD4 p $ "Variable no declarada " ++ ppName n
  Just ty -> return (ty, TV var ty)
tcTy (Const _ k@(CNat _)) _ _ = return (NatTy, TConst k NatTy)
tcTy (Print _ str t) bs ts = do
  (ty, t') <- tcTy t bs ts
  expect NatTy ty t
  return (ty, TPrint str t' ty)
tcTy (IfZ _ c t t') bs ts = do
  (tyc, ttmC) <- tcTy c bs ts
  expect NatTy tyc c
  (tyt, ttmT) <- tcTy t bs ts
  (tyt', ttmT') <- tcTy t' bs ts
  expect tyt tyt' t'
  return (tyt, TIfZ ttmC ttmT ttmT' tyt)
tcTy (Lam _ v ty t) bs ts = do
  (ty', t') <- tcTy t bs (ty : ts) -- No abre terminos
  return (FunTy ty ty', TLam v ty t' (FunTy ty ty'))
tcTy (App _ t u) bs ts = do
  (tyt, t') <- tcTy t bs ts
  (domm, codd) <- domCod t tyt
  (tyu, u') <- tcTy u bs ts
  expect domm tyu u
  return (codd, TApp t' u' domm codd)
tcTy (Fix p f fty x xty t) bs ts = do
  (domm, codd) <- domCod (V p (Free f)) fty
  when (domm /= xty) $ do
    failPosFD4
      p
      "El tipo del argumento de un fixpoint debe coincidir con el \
      \dominio del tipo de la función"
  (ty', t') <- tcTy t bs (xty : fty : ts)
  expect codd ty' t
  return (fty, TFix f fty x xty t' fty)
tcTy (Let _ v ty def t) bs ts = do
  (ty', t') <- tcTy def bs ts
  expect ty ty' def
  (ty'', t'') <- tcTy t bs (ty : ts)
  return $ (ty'', TLet v ty t' t'' ty'')
tcTy (BinaryOp _ op t u) bs ts = do
  (tty, t') <- tcTy t bs ts
  expect NatTy tty t
  (uty, u') <- tcTy u bs ts
  expect NatTy uty u
  return $ (NatTy, TBinaryOp op t' u' NatTy)

changeTy :: TTerm -> Ty -> TTerm
changeTy (TV var _) t = TV var t
changeTy (TConst c _) t = TConst c t
changeTy (TLam n ty tm _) t = TLam n ty tm t
changeTy (TApp tm1 tm2 ty _) t = TApp tm1 tm2 ty t
changeTy (TPrint str tm _) t = TPrint str tm t
changeTy (TBinaryOp bop tm1 tm2 _) t = TBinaryOp bop tm1 tm2 t
changeTy (TFix f fTy var varTy tm _) t = TFix f fTy var varTy tm t
changeTy (TIfZ tmb tmt tmf _) t = TIfZ tmb tmt tmf t
changeTy (TLet name ty tm tm' _) t = TLet name ty tm tm' t

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