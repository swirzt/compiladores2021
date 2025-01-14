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
module Elab
  ( elab,
    desugarDecl,
    desugarTy,
    resugarTy,
    resugar,
    resugarDecl,
  )
where

import Lang
import MonadFD4
import Subst

-- | 'desugar' transforma un termino con azucar sintactico a un NTerm
desugar :: MonadFD4 m => STerm -> m NTerm
desugar (SV info var) = return $ V info var
desugar (SConst info c) = return $ Const info c
desugar (SLam info [] _) =
  failPosFD4 info "No se dio un argumento a la función"
desugar (SLam info (([], _) : _) _) =
  failPosFD4 info "No se dio un argumento a la función"
desugar (SLam info [([n], ty)] stm) = do
  stmDesugar <- desugar stm
  tyDesugar <- desugarTy ty
  return $ Lam info n tyDesugar stmDesugar
desugar (SLam info [(n : ns, ty)] stm) = do
  stmDesugar <- desugar (SLam info [(ns, ty)] stm)
  tyDesugar <- desugarTy ty
  return $ Lam info n tyDesugar stmDesugar
desugar (SLam info (b : bin) stm) = desugar (SLam info [b] $ SLam info bin stm)
desugar (SApp info stm1 stm2) = do
  stm1Desugar <- desugar stm1
  stm2Desugar <- desugar stm2
  return $ App info stm1Desugar stm2Desugar
desugar (SPrint info str stm) = do
  stmDesugar <- desugar stm
  return $ Print info str stmDesugar
desugar (SPrintEta info str) =
  desugar $
    SLam info [(["x"], SNatTy)] (SPrint info str (SV info "x"))
desugar (SBinaryOp info b stm1 stm2) = do
  stm1Desugar <- desugar stm1
  stm2Desugar <- desugar stm2
  return $ BinaryOp info b stm1Desugar stm2Desugar
desugar (SFix info _ _ [] _) = failPosFD4 info "Falta el argumento del fix"
desugar (SFix info _ _ (([], _) : _) _) =
  failPosFD4 info "Falta el argumento del fix"
desugar (SFix info f fty [([n], sty)] stm) = do
  stmDesugar <- desugar stm
  ftyDesugar <- desugarTy fty
  tyDesugar <- desugarTy sty
  return $ Fix info f ftyDesugar n tyDesugar stmDesugar
desugar (SFix info f fty [(n : ns, sty)] stm) = do
  stmDesugar <- desugar (SLam info [(ns, sty)] stm)
  ftyDesugar <- desugarTy fty
  tyDesugar <- desugarTy sty
  return $ Fix info f ftyDesugar n tyDesugar stmDesugar
desugar (SFix info f fty (b : bin) stm) =
  desugar
    (SFix info f fty [b] $ SLam info bin stm)
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
desugar (SLet info f xs lty stmt stmt' False) = do
  stmtDesugar' <- desugar stmt'
  lamDesugar <- desugar $ SLam info xs stmt
  ty <- desugarConcatTy xs lty
  return $ Let info f ty lamDesugar stmtDesugar'
desugar (SLet info _ [] _ _ _ True) =
  failPosFD4 info "Falta el argumento del fix"
desugar (SLet info f [([n], sty)] lty stmt stmt' True) = do
  let fixType = SFunTy sty lty
  stmtDesugar <- desugar $ SFix info f fixType [([n], sty)] stmt
  stmtDesugar' <- desugar stmt'
  fixTyDesugar <- desugarTy fixType
  return $ Let info f fixTyDesugar stmtDesugar stmtDesugar'
desugar (SLet info f [(n : ns, sty)] lty stmt stmt' True) =
  let newTy = nConcatTy (length ns) sty lty
      newTM = SLam info [(ns, sty)] stmt
   in desugar $ SLet info f [([n], sty)] newTy newTM stmt' True
desugar (SLet info f (b : bin) lty stmt stmt' True) =
  let newTM = SLam info bin stmt
      newTy = concatTy bin lty
   in desugar $ SLet info f [b] newTy newTM stmt' True

desugarTy :: MonadFD4 m => STy -> m Ty
desugarTy SNatTy = return NatTy
desugarTy (SFunTy a b) = do
  a' <- desugarTy a
  b' <- desugarTy b
  return $ FunTy a' b'
desugarTy (SVarTy n) = do
  ss <- lookupTyDef n
  case ss of
    Nothing ->
      failFD4 $
        "El tipo " ++ show n ++ " no se encuentra declarado en el entorno."
    Just ty -> return $ NameTy n ty

nConcatTy :: Int -> STy -> STy -> STy
nConcatTy 1 t1 t2 = SFunTy t1 t2 -- No debería llegar a n = 0
nConcatTy n t1 t2 = SFunTy t1 (nConcatTy (n - 1) t1 t2)

concatTy :: [([a], STy)] -> STy -> STy
concatTy [] t = t
concatTy ((ys, sty) : xs) t = nConcatTy (length ys) sty (concatTy xs t)

desugarConcatTy :: MonadFD4 m => [([a], STy)] -> STy -> m Ty
desugarConcatTy xs a = desugarTy $ concatTy xs a

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
elab' env (Fix p f fty x xty t) =
  Fix p f fty x xty (closeN [f, x] (elab' (x : f : env) t))
elab' env (IfZ p c t e) = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operador Print
elab' env (Print i str t) = Print i str (elab' env t)
-- Operadores binarios
elab' env (BinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Aplicaciones generales
elab' env (App p h a) = App p (elab' env h) (elab' env a)
elab' env (Let p v vty def body) =
  Let p v vty (elab' env def) (close v (elab' (v : env) body))

desugarDecl :: MonadFD4 m => SDecl STerm -> m (Decl STerm)
desugarDecl (SDeclFun pos name vars ty def False) = do
  tyDesugar <- desugarConcatTy vars ty
  case vars of
    [] -> return $ DeclFun pos name tyDesugar def
    _ -> return $ DeclFun pos name tyDesugar (SLam pos vars def)
desugarDecl (SDeclFun pos name vars ty def True) = do
  tyDesugar <- desugarConcatTy vars ty
  return $
    DeclFun pos name tyDesugar (SFix pos name (concatTy vars ty) vars def)
desugarDecl _ = failFD4 "Si llegué acá algo esta mal jej"

-- Cantidad total de variables, considerando multibinders
numVars :: [([Name], STy)] -> Int
numVars xs =
  let xs' = map (\(ys, _) -> length ys) xs
   in foldl (+) 0 xs'

getCodom :: Ty -> Ty
getCodom a@(FunTy _ _) = tcodom a
getCodom (NameTy _ t) = getCodom t
getCodom _ = undefined

resugarDecl :: MonadFD4 m => Decl STerm -> m (SDecl STerm)
resugarDecl (DeclFun pos name ty def) = do
  let sty = resugarTy ty
  case def of
    SLam _ vars tt -> do
      let typeF = (iterate getCodom ty) !! (numVars vars)
          typeFR = resugarTy typeF
      return $ SDeclFun pos name vars typeFR tt False
    SFix _ fname _ vars tt ->
      if name == fname
        then do
          let typeF = (iterate getCodom ty) !! (numVars vars)
              typeFR = resugarTy typeF
          return $ SDeclFun pos fname vars typeFR tt True
        else return $ SDeclFun pos name [] sty def False
    _ -> return $ SDeclFun pos name [] sty def False
resugarDecl _ = failFD4 "Si llegué acá algo esta mal jej"

resugar :: MonadFD4 m => NTerm -> m STerm
resugar (V info var) = return $ SV info var
resugar (Const info c) = return $ SConst info c
resugar (Lam info fv tv tm) = do
  stm <- resugar tm
  let tvs = resugarTy tv
  case stm of
    SLam _ ((var, tyVarS) : xs) tms ->
      if tyVarS == tvs
        then return $ SLam info ((fv : var, tyVarS) : xs) tms
        else return $ SLam info (([fv], tvs) : (var, tyVarS) : xs) tms
    SPrint _ str (SV _ fvp) ->
      if fv == fvp
        then return $ SPrintEta info str
        else return $ SLam info [([fv], tvs)] stm
    _ -> return $ SLam info [([fv], tvs)] stm
resugar (App info tm1 tm2) = do
  stm1 <- resugar tm1
  stm2 <- resugar tm2
  return $ SApp info stm1 stm2
resugar (Print info str tm) =
  resugar tm >>= \stm -> return $ SPrint info str stm
resugar (BinaryOp info bo tm1 tm2) = do
  stm1 <- resugar tm1
  stm2 <- resugar tm2
  return $ SBinaryOp info bo stm1 stm2
resugar (Fix info nf tf nv tv tm) = do
  stm <- resugar tm
  let tfs = resugarTy tf
      tvs = resugarTy tv
  case stm of
    SLam _ ((var, tyVarS) : xs) tms ->
      if tyVarS == tvs
        then return $ SFix info nf tfs ((nv : var, tyVarS) : xs) tms
        else return $ SFix info nf tfs (([nv], tyVarS) : (var, tyVarS) : xs) tms
    _ -> return $ SFix info nf tfs [([nv], tvs)] stm
resugar (Let info nv tv tt tm) = do
  stt <- resugar tt
  stm <- resugar tm
  let stv = resugarTy tv
  case stt of
    SFix _ nf _ xs tms ->
      if nv == nf
        then do
          let typeF = (iterate getCodom tv) !! (numVars xs)
              typeFR = resugarTy typeF
          return $ SLet info nf xs typeFR tms stm True
        else return $ SLet info nv [] stv stt stm False
    SLam _ xs tm2 -> do
      let typeF = (iterate getCodom tv) !! (numVars xs) --Para obtener el codominio n veces
          typeFR = resugarTy typeF
      return $ SLet info nv xs typeFR tm2 stm False
    _ -> return $ SLet info nv [] stv stt stm False
resugar (IfZ info tmb tmt tmf) = do
  stmb' <- resugar tmb
  stmt' <- resugar tmt
  stmf' <- resugar tmf
  return $ SIfZ info stmb' stmt' stmf'

resugarTy :: Ty -> STy
resugarTy NatTy = SNatTy
resugarTy (FunTy x y) =
  let xx = resugarTy x
      yy = resugarTy y
   in (SFunTy xx yy)
resugarTy (NameTy n _) = SVarTy n