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

module Elab ( elab, desugarDecl, desugarTy ) where

import MonadFD4  

import Lang
import Subst
import MonadFD4 (failPosFD4, failFD4, lookupTyDef)

-- | 'desugar' transforma un termino con azucar sintactico a un NTerm
desugar :: MonadFD4 m => STerm -> m NTerm
desugar (SV info var) = return $ V info var

desugar (SConst info const) = return $ Const info const

desugar (SLam info [] _) = failPosFD4 info "No se dio un argumento a la función"
desugar (SLam info [(n,ty)] stm) = do stmDesugar <- desugar stm
                                      tyDesugar <- desugarTy ty
                                      return $ Lam info n tyDesugar stmDesugar

desugar (SLam info ((n,ty):xs) stm) = do stmDesugar <- desugar (SLam info xs stm)
                                         tyDesugar <- desugarTy ty
                                         return $ Lam info n tyDesugar stmDesugar

desugar (SApp info stm1 stm2) = do stm1Desugar <- desugar stm1
                                   stm2Desugar <- desugar stm2
                                   return $ App info stm1Desugar stm2Desugar

desugar (SPrint info str stm) = do stmDesugar <- desugar stm
                                   return $ Print info str stmDesugar

desugar (SBinaryOp info b stm1 stm2) = do stm1Desugar <- desugar stm1
                                          stm2Desugar <- desugar stm2
                                          return $ BinaryOp info b stm1Desugar stm2Desugar

desugar (SFix info _ _ [] _) = failPosFD4 info "Falta el argumento del fix"
desugar (SFix info f fty [(n,sty)] stm) = do stmDesugar <- desugar stm
                                             ftyDesugar <- desugarTy fty
                                             tyDesugar <- desugarTy sty
                                             return $ Fix info f ftyDesugar n tyDesugar stmDesugar

desugar (SFix info f fty ((n,sty):xs) stm) = do stmDesugar <- desugar (SLam info xs stm)
                                                ftyDesugar <- desugarTy fty
                                                tyDesugar <- desugarTy sty
                                                return $ Fix info f ftyDesugar n tyDesugar stmDesugar

desugar (SIfZ info stmb stmt stmf) = do stmb' <- desugar stmb
                                        stmt' <- desugar stmt
                                        stmf' <- desugar stmf
                                        return $ IfZ info stmb' stmt' stmf'

desugar (SLet info f [] lty stmt stmt' False) = do stmtDesugar <- desugar stmt
                                                   stmtDesugar' <- desugar stmt'
                                                   tyDesugar <- desugarTy lty
                                                   return $ Let info f tyDesugar stmtDesugar stmtDesugar'
desugar (SLet info _ [] _ _ _ True) = failPosFD4 info "Falta el argumento del fix"
desugar (SLet info f [(n,sty)] lty stmt stmt' True) = do  stmtDesugar <- desugar $ SFix info f (SFunTy sty lty) [(n,sty)] stmt
                                                          stmtDesugar' <- desugar stmt'
                                                          styDesugar <- desugarTy sty
                                                          ltyDesugar <- desugarTy lty
                                                          return $ Let info f (FunTy styDesugar ltyDesugar) stmtDesugar stmtDesugar'
desugar (SLet info f ((n,sty):xs) lty stmt stmt' True) = do stmtDesugar <- desugar $ SLet info f [(n,sty)] (concatTy xs lty) (SLam info xs stmt) stmt' True
                                                            return stmtDesugar
  -- desugar (SLet info f [(n,sty)] lty stmt stmt' False) = Let info f (FunTy sty lty) (desugar $ SLam info [(n,sty)] stmt) (desugar stmt')
desugar (SLet info f xs lty stmt stmt' False) = do stmtDesugar' <- desugar stmt'
                                                   lamDesugar <- desugar $ SLam info xs stmt
                                                   ty <- deconcatTy xs lty
                                                   return $ Let info f ty lamDesugar stmtDesugar'

desugarTy :: MonadFD4 m => STy -> m Ty
desugarTy SNatTy = return NatTy
desugarTy (SFunTy a b) = do a' <- desugarTy a
                            b' <- desugarTy b
                            return $ FunTy a' b'
desugarTy (SVarTy n) = do ss <- lookupTyDef n
                          case ss of
                            Nothing -> failFD4 $ "El tipo " ++ show n ++ " no se encuentra declarado en el entorno." 
                            Just ty -> return $ NameTy n ty

concatTy :: [(a,STy)] -> STy -> STy
concatTy [] a = a
concatTy ((name,sty):xs) a = SFunTy sty (concatTy xs a)

deconcatTy :: MonadFD4 m => [(a,STy)] -> STy -> m Ty
deconcatTy xs a = desugarTy $ concatTy xs a

-- desugar ( Si la primer lista de Let es vacio es sin sugar
-- desugar (SType info Name STy

-- 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab n = do nterm <- desugar n
            return $ elab' [] nterm

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

-- elab_decl :: Decl STerm -> Decl Term
-- elab_decl = fmap elab

desugarDecl :: MonadFD4 m => SDecl STerm -> m (Decl STerm)
desugarDecl (SDeclFun pos name vars ty def False) = do  tyDesugar <- deconcatTy vars ty
                                                        case vars of
                                                          [] -> return $ DeclFun pos name tyDesugar def
                                                          _ -> return $ DeclFun pos name tyDesugar (SLam pos vars def)
desugarDecl (SDeclFun pos name vars ty def True)  = do  tyDesugar <- deconcatTy vars ty
                                                        return $ DeclFun pos name tyDesugar (SFix pos name ty vars def)
desugarDecl _ = failFD4 "Si llegué acá algo esta mal jej"