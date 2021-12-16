module CEK where

import Common (Pos (NoPos))
import Lang
import MonadFD4
import Prelude

data Val
  = Num Int
  | Clos ClosCEK
  deriving (Show)

data ClosCEK
  = ClosFun Env Term Term
  | ClosFix Env Term Term --El segundo Term es para reconstruir la funcion
  deriving (Show)

type Env = [Val]

data Frame
  = FAppL Env Term
  | FAppR ClosCEK
  | FIfz Env Term Term
  | FOpL Env BinaryOp Term
  | FOpR Int BinaryOp
  | FPrint String
  | FLet Env Term
  deriving (Show)

type Kont = [Frame]

search :: MonadFD4 m => Term -> Env -> Kont -> m Val
search (Print _ str t) env kont = search t env (FPrint str : kont)
search (BinaryOp _ op t t') env kont = search t env (FOpL env op t' : kont)
search (IfZ _ t true false) env kont = search t env (FIfz env true false : kont)
search (App _ t t') env kont = search t env (FAppL env t' : kont)
search (V _ (Bound i)) env kont = destroy (env !! i) kont
search (V info (Global i)) env kont = do
  val <- lookupDecl i
  case val of
    Just x -> search x env kont
    Nothing ->
      failPosFD4 info "Error al evaluar el marco de V, variable indefinida"
search (Const _ (CNat c)) _ kont = destroy (Num c) kont
search f@(Lam _ _ _ _) env kont = destroy (Clos $ close f env) kont
search f@(Fix _ _ _ _ _ _) env kont = destroy (Clos $ close f env) kont
search (Let _ _ _ t t') env kont = search t env (FLet env t' : kont)
search (V _ (Free _)) _ _ = undefined -- Para que el linter no moleste, no debería pasar

close :: Term -> Env -> ClosCEK
close f@(Lam _ _ _ t) env = ClosFun env t f
close f@(Fix _ _ _ _ _ t) env = ClosFix env t f
close _ _ = undefined -- Para que el linter no moleste

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy n@(Num m) (FPrint s : xs) = do
  printFD4 $ s ++ show m
  destroy n xs
destroy (Num n) (FOpL e op tm : xs) = search tm e (FOpR n op : xs)
destroy (Num m) (FOpR x op : xs) = case op of
  Add -> destroy (Num $ x + m) xs
  Sub -> destroy (Num $ max 0 (x - m)) xs
destroy (Num 0) (FIfz e t1 _ : xs) = search t1 e xs
destroy (Num _) (FIfz e _ t2 : xs) = search t2 e xs
destroy (Clos clos) (FAppL e tm : xs) = search tm e (FAppR clos : xs)
destroy v (FAppR clos : xs) = case clos of
  ClosFun e tm _ -> search tm (v : e) xs
  a@(ClosFix e tmx _) -> search tmx (v : Clos a : e) xs
destroy v (FLet e tm : xs) = search tm (v : e) xs
destroy v [] = return v
destroy _ (FPrint _ : _) = failFD4 "Error, quise imprimir un fun o fix." -- Creo que este no es necesario, daría error de tipo antes
destroy _ _ = undefined -- Para que el linter no moleste

open :: Val -> Term
open (Num c) = Const NoPos (CNat c)
open (Clos (ClosFun _ _ f)) = f
open (Clos (ClosFix _ _ f)) = f

evalCEK :: MonadFD4 m => Term -> m Term
evalCEK t = do
  tm <- search t [] []
  return $ open tm