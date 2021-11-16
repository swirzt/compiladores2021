module ClosureConvert where

import C
import Control.Monad.State
import Control.Monad.Writer
import Debug.Trace (traceM)
import IR
import Lang
import MonadFD4 (printFD4Debug)
import Subst
import System.IO

--Como en freshen pero para obtener un nombre nuevo
--Aumento el contador cuando saco uno
generateName :: Name -> StateT Int (Writer [IrDecl]) Name
generateName n = do
  k <- get
  modify (+ 1)
  return $ n ++ show k

makeLet :: Ir -> Name -> [Name] -> Ir
makeLet tm name xs = foldr (\(x, y) r -> IrLet x (IrAccess (IrVar name) y) r) tm (zip xs [1 ..])

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ var) = case var of
  Free name -> return $ IrVar name
  Global name -> return $ IrGlobal name
  Bound n -> undefined
closureConvert (Const _ var) = return $ IrConst var
closureConvert (Lam _ name _ tm) = do
  let fvars = freeVars tm
  vname <- generateName name -- Le damos un nombre unico a la variable ligada
  let ttm = open vname tm -- La abrimos
  itm <- closureConvert ttm -- hacemos la clausura del termino
  fname <- generateName "f" -- nombre unico para la funcion
  let cname = "closure" ++ fname -- nombre unico para la clausura
  let itm' = makeLet itm cname fvars -- fijamos el acceso a variables libres
  tell [IrFun fname [cname, vname] itm'] -- guardamos la declaracion top-level
  return $ MkClosure fname (fmap IrVar fvars) -- retornamos el makeClosure
closureConvert (App _ tm1 tm2) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  fname <- generateName "t"
  let newdef = IrVar fname
  return $ IrLet fname itm1 $ IrCall (IrAccess newdef 0) [newdef, itm2]
closureConvert (Print _ str tm) = do
  itm <- closureConvert tm
  return $ IrPrint str itm
closureConvert (BinaryOp _ bop tm1 tm2) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  return $ IrBinaryOp bop itm1 itm2
closureConvert (IfZ _ tb tt tf) = do
  tb' <- closureConvert tb
  tt' <- closureConvert tt
  tf' <- closureConvert tf
  return $ IrIfZ tb' tt' tf'
closureConvert (Fix _ fn _ vn _ tm) = do
  let fvars = freeVars tm
  vname <- generateName vn
  fname <- generateName fn
  let ttm = openN [vname, fname] tm
  itm <- closureConvert ttm
  frname <- generateName "fr" -- nombre unico para la funcion
  let cname = "closure" ++ fname -- nombre unico para la clausura
  let itm' = makeLet itm cname (fname : vname : fvars) -- fijamos el acceso a variables libres
  tell [IrFun fname [cname, vname] itm']
  return $ MkClosure fname (fmap IrVar fvars)
closureConvert (Let _ name _ tn tm) = do
  vname <- generateName name
  let ttm = open vname tm
  itn <- closureConvert tn
  itm <- closureConvert ttm
  return $ IrLet vname itn itm

runCC :: Int -> [Decl Term] -> [IrDecl]
runCC _ [] = []
runCC n (decl : xs) = case decl of
  DeclType {} -> runCC n xs
  DeclFun _ name ty tt ->
    let ((ir, k), xx) = runWriter $ runStateT (closureConvert tt) n
        y = runCC k xs
     in IrVal name ir : xx ++ y

compilaC :: [Decl Term] -> String
compilaC xs = ir2C $ IrDecls $ runCC 0 xs

cWrite :: String -> FilePath -> IO ()
cWrite cp filename = writeFile filename cp