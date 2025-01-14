{-# LANGUAGE DeriveFunctor #-}

-- |
-- Module      : Lang
-- Description : AST de términos, declaraciones y tipos
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
--
-- Definiciones de distintos tipos de datos:
--   - AST de términos
--   - Declaraciones
--   - Tipos
--   - Variables
module Lang where

import Common (Pos)
import Data.List.Extra (nubSort)

-- | AST de Tipos
data Ty
  = NatTy
  | FunTy {tdom :: Ty, tcodom :: Ty} -- Mal planeamiento a futuro
  | NameTy Name Ty
  deriving (Show, Ord)

instance Eq Ty where
  NatTy == NatTy = True
  NatTy == FunTy _ _ = False
  FunTy _ _ == NatTy = False
  FunTy x y == FunTy w z = x == w && y == z
  NameTy _ t == x = t == x
  x == NameTy _ t = x == t

-- | AST de Tipos con Sugar
data STy
  = SNatTy
  | SFunTy {dom :: STy, codom :: STy}
  | SVarTy Name
  deriving (Show, Eq)

type Name = String

newtype Const = CNat Int
  deriving (Show, Eq)

data BinaryOp
  = Add
  | Sub
  deriving (Show, Eq)

-- | tipo de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración
data Decl a
  = DeclType {declPos :: Pos, declName :: Name, declType :: Ty}
  | DeclFun {declPos :: Pos, declName :: Name, declType :: Ty, declBody :: a}
  deriving (Show, Functor)

data SDecl a
  = SDeclType Pos Name STy
  | SDeclFun
      { sdeclPos :: Pos,
        sdeclName :: Name,
        sdeclVars :: [([Name], STy)],
        sdeclType :: STy,
        sdeclDef :: a,
        sdeclRec :: Bool
      }
  deriving (Show, Functor)

-- | AST de los términos.
--   - info es información extra que puede llevar cada nodo.
--       Por ahora solo la usamos para guardar posiciones en el código fuente.
--   - var es el tipo de la variables. Es 'Name' para fully named y 'Var' para locally closed.
data Tm info var
  = V info var
  | Const info Const
  | Lam info Name Ty (Tm info var)
  | App info (Tm info var) (Tm info var)
  | Print info String (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Tm info var)
  deriving (Show, Functor, Eq)

data STm info var
  = SV info var
  | SConst info Const
  | SLam info [([Name], STy)] (STm info var)
  | SApp info (STm info var) (STm info var)
  | SPrint info String (STm info var)
  | SPrintEta info String
  | SBinaryOp info BinaryOp (STm info var) (STm info var)
  | SFix info Name STy [([Name], STy)] (STm info var)
  | SIfZ info (STm info var) (STm info var) (STm info var)
  | SLet info Name [([Name], STy)] STy (STm info var) (STm info var) Bool
  -- Si la primer lista de Let es vacio es sin sugar
  deriving (Show, Functor)

type STerm =
  -- | 'STm' tiene 'Name's como variables ligadas y libres y globales, guarda posición, y azucar sintactico
  STm Pos Name

type NTerm =
  -- | 'Tm' tiene 'Name's como variables ligadas y libres y globales, guarda posición
  Tm Pos Name

type Term =
  -- | 'Tm' con índices de De Bruijn como variables ligadas, y nombres para libres y globales, guarda posición
  Tm Pos Var

type TTerm = Tm Ty Var

data Var
  = Bound !Int
  | Free Name
  | Global Name
  deriving (Show, Eq)

-- | Obtiene la info en la raíz del término.
getInfo :: Tm info var -> info
getInfo (V i _) = i
getInfo (Const i _) = i
getInfo (Lam i _ _ _) = i
getInfo (App i _ _) = i
getInfo (Print i _ _) = i
getInfo (Fix i _ _ _ _ _) = i
getInfo (IfZ i _ _ _) = i
getInfo (Let i _ _ _ _) = i
getInfo (BinaryOp i _ _ _) = i

changeInfo :: info2 -> Tm info var -> Tm info2 var
changeInfo i (V _ v) = V i v
changeInfo i (Const _ c) = Const i c
changeInfo i (Lam _ n t tm) = Lam i n t $ changeInfo i tm
changeInfo i (App _ tm1 tm2) = App i (changeInfo i tm1) (changeInfo i tm2)
changeInfo i (Print _ str tm) = Print i str $ changeInfo i tm
changeInfo i (Fix _ fn ft vn vt tm) = Fix i fn ft vn vt $ changeInfo i tm
changeInfo i (IfZ _ t1 t2 t3) =
  IfZ i (changeInfo i t1) (changeInfo i t2) (changeInfo i t3)
changeInfo i (Let _ n t t1 t2) = Let i n t (changeInfo i t1) (changeInfo i t2)
changeInfo i (BinaryOp _ bop t1 t2) =
  BinaryOp i bop (changeInfo i t1) (changeInfo i t2)

-- | Obtiene los nombres de variables (abiertas o globales) de un término.
freeVars :: Tm info Var -> [Name]
freeVars tm = nubSort $ go tm []
  where
    go (V _ (Free v)) xs = v : xs
    go (V _ (Global v)) xs = v : xs
    go (V _ _) xs = xs
    go (Lam _ _ _ t) xs = go t xs
    go (App _ l r) xs = go l $ go r xs
    go (Print _ _ t) xs = go t xs
    go (BinaryOp _ _ t u) xs = go t $ go u xs
    go (Fix _ _ _ _ _ t) xs = go t xs
    go (IfZ _ c t e) xs = go c $ go t $ go e xs
    go (Const _ _) xs = xs
    go (Let _ _ _ e t) xs = go e (go t xs)

freeVarsInfo :: Ord info => Tm info Var -> [(Name, info)]
freeVarsInfo tm = nubSort $ go tm []
  where
    go (V ty (Free v)) xs = (v, ty) : xs
    go (V ty (Global v)) xs = (v, ty) : xs
    go (V _ _) xs = xs
    go (Lam _ _ _ t) xs = go t xs
    go (App _ l r) xs = go l $ go r xs
    go (Print _ _ t) xs = go t xs
    go (BinaryOp _ _ t u) xs = go t $ go u xs
    go (Fix _ _ _ _ _ t) xs = go t xs
    go (IfZ _ c t e) xs = go c $ go t $ go e xs
    go (Const _ _) xs = xs
    go (Let _ _ _ e t) xs = go e (go t xs)