-- |
-- Module      : Subst
-- Description : Define las operaciones de la representacion locally nameless
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
--
-- Este módulo define las operaciones de la representacion locally nameless,
-- y la substitución.
module Subst where

import Common
import Data.List (elemIndex)
import Lang

varChanger ::
  (Int -> Pos -> Name -> Term) -> --que hacemos con las variables localmente libres
  (Int -> Pos -> Int -> Term) -> --que hacemos con los indices de De Bruijn
  Term ->
  Term
varChanger local bound t = go 0 t
  where
    go n (V p (Bound i)) = bound n p i
    go n (V p (Free x)) = local n p x
    go n (V p (Global x)) = V p (Global x)
    go n (Lam p y ty t) = Lam p y ty (go (n + 1) t)
    go n (App p l r) = App p (go n l) (go n r)
    go n (Fix p f fty x xty t) = Fix p f fty x xty (go (n + 2) t)
    go n (IfZ p c t e) = IfZ p (go n c) (go n t) (go n e)
    go n t@(Const _ _) = t
    go n (Print p str t) = Print p str (go n t)
    go n (BinaryOp p op t u) = BinaryOp p op (go n t) (go n u)
    go n (Let p v vty m o) = Let p v vty (go n m) (go (n + 1) o)

-- `openN [nn,..,n0] t` reemplaza las primeras (n+1) variables ligadas
-- en `t` (que debe ser localmente cerrado) por los nombres libres en la
-- lista. La variable Bound 0 pasa a ser Free n0, y etc. Estos nombres
-- deben ser frescos en el término para que no ocurra shadowing.
openN :: [Name] -> Term -> Term
openN ns = varChanger (\_ p n -> V p (Free n)) bnd
  where
    bnd depth p i
      | i < depth = V p (Bound i)
      | i >= depth && i < depth + nns =
        V p (Free (nsr !! (i - depth)))
      | otherwise = abort "openN: M is not LC"
    nns = length ns
    nsr = reverse ns

-- `closeN [nn,..,n0] t` es la operación inversa a open. Reemplaza
-- las variables `Free ni` por la variable ligada `Bound i`.
closeN :: [Name] -> Term -> Term
closeN ns = varChanger lcl (\_ p i -> V p (Bound i))
  where
    lcl depth p y =
      case elemIndex y nsr of
        Just i -> V p (Bound (i + depth))
        Nothing -> V p (Free y)
    nsr = reverse ns

-- `substN [tn,..,t0] t` sustituye los índices de de Bruijn en t con
-- los términos de la lista. Bound 0 pasa a t0, etc. Notar el orden
-- inverso para hacer las llamadas más intuitivas.
--
-- El término `t` debe tener a lo sumo tantos índices abiertos como la
-- longitud de la lista. Si es localmente cerrado (es decir que no tiene
-- índices abiertos), nada va a ser sustituido.
--
-- Puede pensarse como una optimizacíon de primero hacer `open
-- [nn,..,n0] t`, con nombres frescos, y luego sustituir los nombres
-- por los términos correspondientes. La ventaja es que no hace falta
-- generar ningún nombre, y por lo tanto evitamos la necesidad de
-- nombres frescos.
substN :: [Term] -> Term -> Term
substN ns = varChanger (\_ p n -> V p (Free n)) bnd
  where
    bnd depth p i
      | i < depth = V p (Bound i)
      | i >= depth && i < depth + nns =
        nsr !! (i - depth)
      | otherwise = abort "substN: M is not LC"
    nns = length ns
    nsr = reverse ns

-- Algunas definiciones auxiliares:

subst :: Term -> Term -> Term
subst n m = substN [n] m

close :: Name -> Term -> Term
close nm = closeN [nm]

open :: Name -> Term -> Term
open x t = openN [x] t

g2f :: Var -> Var
g2f (Global name) = Free name
g2f x = x

global2Free :: Term -> Term
global2Free = fmap g2f

------Compilar a C
varChangerTTerm ::
  (Int -> Ty -> Name -> TTerm) -> --que hacemos con las variables localmente libres
  (Int -> Ty -> Int -> TTerm) -> --que hacemos con los indices de De Bruijn
  TTerm ->
  TTerm
varChangerTTerm local bound t = go 0 t
  where
    go n (TV (Bound i) t) = bound n t i
    go n (TV (Free x) t) = local n t x
    go n tm@(TV (Global x) t) = tm
    go n (TLam y ty t ty') = TLam y ty (go (n + 1) t) ty'
    go n (TApp l r t1 t2) = TApp (go n l) (go n r) t1 t2
    go n (TFix f fty x xty t ty) = TFix f fty x xty (go (n + 2) t) ty
    go n (TIfZ c t e ty) = TIfZ (go n c) (go n t) (go n e) ty
    go n t@(TConst _ _) = t
    go n (TPrint str t ty) = TPrint str (go n t) ty
    go n (TBinaryOp op t u ty) = TBinaryOp op (go n t) (go n u) ty
    go n (TLet v vty m o ty) = TLet v vty (go n m) (go (n + 1) o) ty

openNTTerm :: [Name] -> TTerm -> TTerm
openNTTerm ns = varChangerTTerm (\_ ty n -> TV (Free n) ty) bnd
  where
    bnd depth ty i
      | i < depth = TV (Bound i) ty
      | i >= depth && i < depth + nns =
        TV (Free (nsr !! (i - depth))) ty
      | otherwise = abort "openN: M is not LC"
    nns = length ns
    nsr = reverse ns

openTTerm :: Name -> TTerm -> TTerm
openTTerm x t = openNTTerm [x] t