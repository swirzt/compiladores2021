module IR where

import Lang

data Ir = IrVar Name
        | IrGlobal Name
        | IrCall Ir [(Ir, Maybe Ty)] Ty Ty
        | IrConst Const
        | IrPrint String Ir
        | IrBinaryOp BinaryOp Ir Ir 
        | IrLet Name Ir Ir Ty Ty
        | IrIfZ Ir Ir Ir Ty
        | MkClosure Name [Ir] Ty
        | IrAccess Ir Int
  deriving Show

data IrDecl =
    IrFun { irDeclName :: Name
          , irDeclArgNames :: [(Name, Maybe Ty)]
          , irDeclBody :: Ir
          , irDeclTy :: Ty
    }
  | IrVal { irDeclName :: Name
          , irDeclDef :: Ir
          , irDeclTy :: Ty
          }
  deriving Show


newtype IrDecls = IrDecls { irDecls :: [IrDecl] }

{-
La siguiente instancia es sólo para debugging
-}
instance Show IrDecls where
  show (IrDecls decls) =
   concatMap (\d -> show d ++ "\n") decls
