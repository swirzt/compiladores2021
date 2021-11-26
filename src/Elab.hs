-- |
-- Module      : Elab
-- Description : Elabora un término fully named a uno locally closed.
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
--
-- Este módulo permite elaborar términos y declaraciones para convertirlas desde
-- fully named (@NTerm) a locally closed (@Term@)
module Elab (elab, desugarDecl, desugarTy, resugarTy, resugar, resugarDecl) where

import Lang
import MonadFD4
import Subst

-- | 'desugar' transforma un termino con azucar sintactico a un NTerm
desugar :: MonadFD4 m => STerm -> m NTerm
desugar (SV info var) = return $ V info var
desugar (SConst info const) = return $ Const info const
desugar (SLam info [] _) = failPosFD4 info "No se dio un argumento a la función"
desugar (SLam info [(n, ty)] stm) = do
  stmDesugar <- desugar stm
  tyDesugar <- desugarTy ty
  return $ Lam info n tyDesugar stmDesugar
desugar (SLam info ((n, ty) : xs) stm) = do
  stmDesugar <- desugar (SLam info xs stm)
  tyDesugar <- desugarTy ty
  return $ Lam info n tyDesugar stmDesugar
desugar (SApp info stm1 stm2) = do
  stm1Desugar <- desugar stm1
  stm2Desugar <- desugar stm2
  return $ App info stm1Desugar stm2Desugar
desugar (SPrint info str stm) = do
  stmDesugar <- desugar stm
  return $ Print info str stmDesugar
desugar (SPrintEta info str) = desugar $ SLam info [("x", SNatTy)] (SPrint info str (SV info "x"))
desugar (SBinaryOp info b stm1 stm2) = do
  stm1Desugar <- desugar stm1
  stm2Desugar <- desugar stm2
  return $ BinaryOp info b stm1Desugar stm2Desugar
desugar (SFix info _ _ [] _) = failPosFD4 info "Falta el argumento del fix"
desugar (SFix info f fty [(n, sty)] stm) = do
  stmDesugar <- desugar stm
  ftyDesugar <- desugarTy fty
  tyDesugar <- desugarTy sty
  return $ Fix info f ftyDesugar n tyDesugar stmDesugar
desugar (SFix info f fty ((n, sty) : xs) stm) = do
  stmDesugar <- desugar (SLam info xs stm)
  ftyDesugar <- desugarTy fty
  tyDesugar <- desugarTy sty
  return $ Fix info f ftyDesugar n tyDesugar stmDesugar
desugar (SIfZ info stmb stmt stmf) = do
  stmb' <- desugar stmb
  stmt' <- desugar stmt
  stmf' <- desugar stmf
  return $ IfZ info stmb' stmt' stmf'
desugar (SLet info f [] lty stmt stmt' False) = do
  stmtDesugar <- desugar stmt
  stmtDesugar' <- desugar stmt'
  tyDesugar <- desugarTy lty
  return $ Let info f tyDesugar stmtDesugar stmtDesugar'
desugar (SLet info _ [] _ _ _ True) = failPosFD4 info "Falta el argumento del fix"
desugar (SLet info f [(n, sty)] lty stmt stmt' True) = do
  let fixType = SFunTy sty lty
  stmtDesugar <- desugar $ SFix info f fixType [(n, sty)] stmt
  stmtDesugar' <- desugar stmt'
  fixTyDesugar <- desugarTy fixType
  return $ Let info f fixTyDesugar stmtDesugar stmtDesugar'
desugar (SLet info f ((n, sty) : xs) lty stmt stmt' True) = desugar $ SLet info f [(n, sty)] (concatTy xs lty) (SLam info xs stmt) stmt' True
desugar (SLet info f xs lty stmt stmt' False) = do
  stmtDesugar' <- desugar stmt'
  lamDesugar <- desugar $ SLam info xs stmt
  ty <- desugarConcatTy xs lty
  return $ Let info f ty lamDesugar stmtDesugar'

desugarTy :: MonadFD4 m => STy -> m Ty
desugarTy SNatTy = return NatTy
desugarTy (SFunTy a b) = do
  a' <- desugarTy a
  b' <- desugarTy b
  return $ FunTy a' b'
desugarTy (SVarTy n) = do
  ss <- lookupTyDef n
  case ss of
    Nothing -> failFD4 $ "El tipo " ++ show n ++ " no se encuentra declarado en el entorno."
    Just ty -> return $ NameTy n ty

concatTy :: [(a, STy)] -> STy -> STy
concatTy [] a = a
concatTy ((name, sty) : xs) a = SFunTy sty (concatTy xs a)

desugarConcatTy :: MonadFD4 m => [(a, STy)] -> STy -> m Ty
desugarConcatTy xs a = desugarTy $ concatTy xs a

-- desugar ( Si la primer lista de Let es vacio es sin sugar
-- desugar (SType info Name STy

-- 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado.
elab :: MonadFD4 m => STerm -> m Term
elab n = do
  nterm <- desugar n
  return $ elab' [] nterm

elab' :: [Name] -> NTerm -> Term
elab' env (V p v) =
  -- Tenemos que hver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then V p (Free v)
    else V p (Global v)
elab' _ (Const p c) = Const p c
elab' env (Lam p v ty t) = Lam p v ty (close v (elab' (v : env) t))
elab' env (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab' (x : f : env) t))
elab' env (IfZ p c t e) = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operador Print
elab' env (Print i str t) = Print i str (elab' env t)
-- Operadores binarios
elab' env (BinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Aplicaciones generales
elab' env (App p h a) = App p (elab' env h) (elab' env a)
elab' env (Let p v vty def body) = Let p v vty (elab' env def) (close v (elab' (v : env) body))

desugarDecl :: MonadFD4 m => SDecl STerm -> m (Decl STerm)
desugarDecl (SDeclFun pos name vars ty def False) = do
  tyDesugar <- desugarConcatTy vars ty
  case vars of
    [] -> return $ DeclFun pos name tyDesugar def
    _ -> return $ DeclFun pos name tyDesugar (SLam pos vars def)
desugarDecl (SDeclFun pos name vars ty def True) = do
  tyDesugar <- desugarConcatTy vars ty
  return $ DeclFun pos name tyDesugar (SFix pos name (concatTy vars ty) vars def)
desugarDecl _ = failFD4 "Si llegué acá algo esta mal jej"

resugarDecl :: MonadFD4 m => Decl STerm -> m (SDecl STerm)
resugarDecl (DeclFun pos name ty def) = do
  sty <- resugarTy ty
  case def of
    SLam _ vars tt -> return $ SDeclFun pos name vars ((iterate codom sty) !! (length vars)) tt False
    SFix _ fname fty vars tt -> if name == fname
                                then return $ SDeclFun pos fname vars ((iterate codom sty) !! (length vars)) tt True
                                else return $ SDeclFun pos name [] sty def False
    _ -> return $ SDeclFun pos name [] sty def False
resugarDecl _ = failFD4 "Si llegué acá algo esta mal jej"

resugar :: MonadFD4 m => NTerm -> m STerm
resugar (V info var) = return $ SV info var
resugar (Const info c) = return $ SConst info c
resugar (Lam info fv tv tm) = do
  stm <- resugar tm
  tvs <- resugarTy tv
  case stm of
    SLam _ xs tms -> return $ SLam info ((fv, tvs) : xs) tms
    SPrint _ str (SV _ fvp) ->
      if fv == fvp
        then return $ SPrintEta info str
        else return $ SLam info [(fv, tvs)] stm
    _ -> return $ SLam info [(fv, tvs)] stm
resugar (App info tm1 tm2) = do
  stm1 <- resugar tm1
  stm2 <- resugar tm2
  return $ SApp info stm1 stm2
resugar (Print info str tm) = resugar tm >>= \stm -> return $ SPrint info str stm
resugar (BinaryOp info bo tm1 tm2) = do
  stm1 <- resugar tm1
  stm2 <- resugar tm2
  return $ SBinaryOp info bo stm1 stm2
resugar (Fix info nf tf nv tv tm) = do
  stm <- resugar tm
  tfs <- resugarTy tf
  tvs <- resugarTy tv
  case stm of
    SLam _ xs tms -> return $ SFix info nf tfs ((nv, tvs) : xs) tms
    _ -> return $ SFix info nf tfs [(nv, tvs)] stm
resugar (Let info nv tv tt tm) = do
  stt <- resugar tt
  stm <- resugar tm
  stv <- resugarTy tv
  case stt of -- Gano Gurvich
    SFix _ nf stf xs tms ->
      -- Hay que hacer algo con el concat de tipos en el letrec
      if nv == nf
        then return $ SLet info nf xs (codom stf) tms stm True
        else return $ SLet info nv [] stv stt stm False
    SLam _ xs tm2 -> do
      let typeF = (iterate codom stv) !! (length xs) --Para obtener el codominio n veces
      return $ SLet info nv xs typeF tm2 stm False
    _ -> return $ SLet info nv [] stv stt stm False
resugar (IfZ info tmb tmt tmf) = do
  stmb' <- resugar tmb
  stmt' <- resugar tmt
  stmf' <- resugar tmf
  return $ SIfZ info stmb' stmt' stmf'

resugarTy :: MonadFD4 m => Ty -> m STy
resugarTy NatTy = return SNatTy
resugarTy (FunTy x y) = do
  xx <- resugarTy x
  yy <- resugarTy y
  return (SFunTy xx yy)
resugarTy (NameTy n ty) = return $ SVarTy n

-- getTy :: TTerm -> Ty
-- getTy (TV _ t) = t
-- getTy (TConst _ t) = t
-- getTy (TLam _ _ _ t) = t
-- getTy (TApp _ _ t) = t
-- getTy (TPrint _ _ t) = t
-- getTy (TBinaryOp _ _ _ t) = t
-- getTy (TFix _ _ _ _ _ t) = t
-- getTy (TIfZ _ _ _ t) = t
-- getTy (TLet _ _ _ _ t) = t

-- --Consulta para Mauro: ¿En que orden se guardan los tipos en el entorno? ¿Nos complican los indices de deBroin?
-- typer :: MonadFD4 m => Term -> [Ty] -> m TTerm
-- typer (V i var) xs = case var of
--                         Bound k -> return $ TV var (xs !! k)
--                         Global n -> do t <- lookupTy n
--                                        case t of
--                                          Just ty -> return $ TV var ty
--                                          Nothing -> failFD4 "error de tipo" -- No debería
--                         Free n -> failFD4 "No esperabamos variables libres"
-- typer (Const i k) xs = return $ TConst k NatTy
-- typer (Lam i name ty tm) xs = do tm' <- typer tm (ty:xs)
--                                  return $ TLam name ty tm' (getTy tm')
-- typer (App i tm1 tm2) xs = do tm1' <- typer tm1 xs
--                               tm2' <- typer tm2 xs
--                               return $ TApp tm1' tm2' (tcodom $ getTy tm1') --Meter el tipo de tm1'
-- typer (Print i str tm) xs = do tm' <- typer tm xs
--                                return $ TPrint str tm' (getTy tm')
-- typer (BinaryOp i bOp tm1 tm2) xs = do tm1' <- typer tm1 xs
--                                        tm2' <- typer tm2 xs
--                                        return $ TBinaryOp bOp tm1' tm2' NatTy
-- typer (Fix i fName fTy vName vTy tm) xs = do tm' <- typer tm (vTy:fTy:xs)
--                                              return $ TFix fName fTy vName vTy tm' fTy
-- typer (IfZ i tmb tmt tmf) xs = do tmb' <- typer tmb xs
--                                   tmt' <- typer tmt xs
--                                   tmf' <- typer tmf xs
--                                   return $ TIfZ tmb' tmt' tmf' (getTy tmt')
-- typer (Let i vName vTy tm1 tm2) xs = do tm1' <- typer tm1 xs
--                                         tm2' <- typer tm2 (vTy:xs)
--                                         return $ TLet vName vTy tm1' tm2' (getTy tm2')
