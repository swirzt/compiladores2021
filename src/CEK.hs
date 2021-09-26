module CEK where

import Common (Pos (NoPos))
import Lang
import MonadFD4
import PPrint (pp)
import Prelude

data Val = Num Int | Clos ClosCEK
  deriving (Show)

data ClosCEK = ClosFun Env Term Term | ClosFix Env Name Term Term --El segundo Term es para reconstruir la funcion
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
search (Print info str t) env kont = search t env (FPrint str : kont)
search (BinaryOp info op t t') env kont = search t env (FOpL env op t' : kont)
search (IfZ info t true false) env kont = search t env (FIfz env true false : kont)
search (App info t t') env kont = search t env (FAppL env t' : kont)
search (V info (Bound i)) env kont = destroy (env !! i) kont
search (V info (Global i)) env kont = do
  val <- lookupDecl i
  case val of
    Just x -> search x env kont
    Nothing -> failPosFD4 info "Error al evaluar el marco de V, variable indefinida"
search (V info (Free i)) env kont = failPosFD4 info "Preguntarle a Mauro"
search (Const info (CNat c)) env kont = destroy (Num c) kont
search f@(Lam info name ty t) env kont = destroy (Clos $ close f env) kont
search f@(Fix info fname fty xname xty t) env kont = destroy (Clos $ close f env) kont
search (Let info x xty t t') env kont = search t env (FLet env t' : kont)

close :: Term -> Env -> ClosCEK
close f@(Lam _ _ _ t) env = ClosFun env t f
close f@(Fix _ fname fty xname xty t) env = ClosFix env fname t f
close _ _ = undefined -- Para que el linter no moleste

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy n@(Num m) (FPrint s : xs) = do
  printFD4 $ s ++ show m
  destroy n xs
destroy v (FPrint s : xs) = failFD4 "Error, quise imprimir un fun o fix."
destroy (Num n) (FOpL e op tm : xs) = search tm e (FOpR n op : xs)
destroy (Num m) (FOpR x op : xs) = case op of
  Add -> destroy (Num $ x + m) xs
  Sub -> destroy (Num $ x - m) xs
destroy (Num 0) (FIfz e t1 t2 : xs) = search t1 e xs
destroy (Num _) (FIfz e t1 t2 : xs) = search t2 e xs
destroy (Clos clos) (FAppL e tm : xs) = search tm e (FAppR clos : xs)
destroy v (FAppR clos : xs) = case clos of
  ClosFun e tm _ -> search tm (v : e) xs
  a@(ClosFix e tmf tmx _) -> search tmx (v : Clos a : e) xs
destroy v (FLet e tm : xs) = search tm (v : e) xs
destroy v [] = return v
destroy x k = undefined -- Para que el linter no moleste

open :: Val -> Term
open (Num c) = Const NoPos (CNat c)
open (Clos (ClosFun _ _ f)) = f
open (Clos (ClosFix _ _ _ f)) = f

evalCEK :: MonadFD4 m => Term -> m Term
evalCEK t = do
  tm <- search t [] []
  return $ open tm