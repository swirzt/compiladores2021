{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@NTerm) a locally closed (@Term@) 
-}

module Elab ( elab, elab_decl ) where

import Lang
import Subst

-- | 'desugar' transforma un termino con azucar sintactico a un NTerm
desugar :: MonadFD4 m => STerm -> m NTerm
desugar (SV info var) = V Info Var

desugar (SConst info const) = Const info const

desugar (SLam info [] _) = failPosFD4 info "No se dio un argumento a la función"
desugar (SLam info [(n,ty)] stm) = do stmDesugar <- desugar stm
                                      return $ Lam info n ty stmDesugar

desugar (SLam info ((n,ty):xs) stm) = do stmDesugar <- desugar (SLam info xs stm)
                                         return $ Lam info n ty stmDesugar

desugar (SApp info stm1 stm2) = do stm1Desugar <- desugar stm1
                                   stm2Desugar <- desugar stm2
                                   retur $ App info stm1Desugar stm2Desugar 

desugar (SPrint info str stm) = do stmDesugar <- desugar stm
                                   return $ Print info str stmDesugar

desugar (SBinaryOp info b stm1 stm2) = do stm1Desugar <- desugar stm1
                                          stm2Desugar <- desugar stm2
                                          return $ BinaryOp info b stm1Desugar stm2Desugar

desugar (SFix info _ _ [] _) = failPosFD4 info "Falta el argumento del fix"
desugar (SFix info f fty [(n,sty)] stm) = do stmDesugar <- desugar stm
                                             return $ Fix info f fty n sty stmDesugar
desugar (SFix info f fty ((n,sty):xs) stm) = do stmDesugar <- desugar (SLam info xs stm)
                                                return $ Fix info f fty n sty stmDesugar 

desugar (SIfZ info stmb stmt stmf) = do stmb' <- desugar stmb
                                        stmt' <- desugar stmt
                                        stmf' <- desugar stmf
                                        return $ IfZ info stmb' stmt' stmf'

desugar (SLet info f [] lty stmt stmt' False) = Let info f lty (desugar stmt) (desugar stmt')
desugar (SLet info _ [] _ _ _ True) = failPosFD4
desugar (SLet info f [(n,sty)] lty stmt stmt' True) = Let info f (FunTy sty lty) (desugar $ SFix info f (FunTy sty lty) [(n,sty)] stmt) (desugar stmt')
desugar (SLet info f ((n,sty):xs) lty stmt stmt' True) = desugar $ SLet info f [(n,sty)] (concatTy xs lty) (SLam info xs stmt) stmt' True
-- desugar (SLet info f [(n,sty)] lty stmt stmt' False) = Let info f (FunTy sty lty) (desugar $ SLam info [(n,sty)] stmt) (desugar stmt')
desugar (SLet info f xs lty stmt stmt' False) = Let info f (concatTy xs lty) (desugar $ SLam info xs stmt) stmt' 

desugarTy :: STy -> Ty
desugarTy SNatTy = NatTy
desugarTy SFunTy a b = FunTy (desugarTy a) (desugarTy b) 

concatTy :: [(a,STy)] -> STy -> Ty
concatTy [] a = desugarTy a
concatTy (x:xs) a = FunTy (desugarTy x) (concatTy xs a)

-- desugar ( Si la primer lista de Let es vacio es sin sugar
-- desugar (SType info Name STy

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: NTerm -> Term
elab = elab' []

elab' :: [Name] -> NTerm -> Term
elab' env (V p v) =
  -- Tenemos que hver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then  V p (Free v)
    else V p (Global v)

elab' _ (Const p c) = Const p c
elab' env (Lam p v ty t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab' (x:f:env) t))
elab' env (IfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operador Print
elab' env (Print i str t) = Print i str (elab' env t)
-- Operadores binarios
elab' env (BinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Aplicaciones generales
elab' env (App p h a) = App p (elab' env h) (elab' env a)
elab' env (Let p v vty def body) = Let p v vty (elab' env def) (close v (elab' (v:env) body))

elab_decl :: Decl NTerm -> Decl Term
elab_decl = fmap elab
