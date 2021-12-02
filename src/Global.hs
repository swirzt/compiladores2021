-- |
-- Module      : Global
-- Description : Define el estado global del compilador
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
module Global where

import Lang

{-
 Tipo para representar las banderas disponibles en línea de comando.
 Está en este módulo para poder definirlo en el entorno global
-}
data Mode
  = Interactive
  | Typecheck
  | InteractiveCEK
  | Bytecompile
  | RunVM
  | CC

data GlEnv = GlEnv
  { inter :: Bool, --  ^ True, si estamos en modo interactivo.

    -- | Último archivo cargado.
    lfile :: String,
    -- | Cantidad de declaraciones desde la última carga
    cantDecl :: Int,
    -- | Entorno con declaraciones globales
    glb :: [Decl Term],
    -- | Entorno de tipado de declaraciones globales
    tyEnv :: [(Name, Ty)],
    -- | Entorno de tipos definidos
    typeDefs :: [(Name, Ty)],
    -- | Modo de ejecución del entorno interactivo
    mode :: Maybe Mode,
    -- | Si se quiere optimizar los términos
    opti :: Bool,
    -- | Si se optimizó el término en la última pasada
    optimized :: Bool,
    -- | Generador de nombres frescos
    fresh :: Int
  }

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv True "" 0 [] [] [] Nothing False False 0
