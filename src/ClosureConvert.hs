module ClosureConvert where

import C
import Control.Monad.State
import Control.Monad.Writer
import Debug.Trace (traceM)
import IR
import Lang
import Subst

--Como en freshen pero para obtener un nombre nuevo
--Aumento el contador cuando saco uno
generateName :: Name -> StateT (Int, [Name]) (Writer [IrDecl]) Name
generateName n = do
  (k, _) <- get
  modify (\(h, vars) -> (h + 1, vars))
  return $ n ++ show k

makeLet :: Ir -> Name -> [Name] -> Bool -> Ir
makeLet tm name xs False = makeLet' tm name xs 1
makeLet tm _ [] True = tm
makeLet tm name (x : xs) True = IrLet x (IrVar name) (makeLet' tm name xs 2)

makeLet' :: Ir -> Name -> [Name] -> Int -> Ir
makeLet' tm name xs n = foldr (\(x, y) r -> IrLet x (IrAccess (IrVar name) y) r) tm (zip xs [n ..])

closureConvert :: Term -> StateT (Int, [Name]) (Writer [IrDecl]) Ir
closureConvert (V _ var) = case var of
  Free name -> return $ IrVar name
  Global name -> return $ IrGlobal name
  Bound n -> undefined
closureConvert (Const _ var) = return $ IrConst var
closureConvert (Lam _ name _ tm) = do
  (_, fvars) <- get
  vname <- generateName name -- Le damos un nombre unico a la variable ligada
  let ttm = open vname tm -- La abrimos
  modify (\(k, vars) -> (k, vname : vars))
  itm <- closureConvert ttm -- hacemos la clausura del termino
  fname <- generateName "f" -- nombre unico para la funcion
  let cname = "closure" ++ fname -- nombre unico para la clausura
  let itm' = makeLet itm cname fvars False -- fijamos el acceso a variables libres
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
  pname <- generateName "p"
  return $ IrLet pname itm $ IrPrint str $ IrVar pname
closureConvert (BinaryOp _ bop tm1 tm2) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  return $ IrBinaryOp bop itm1 itm2
closureConvert (IfZ _ tb tt tf) = do
  tb' <- closureConvert tb
  tt' <- closureConvert tt
  tf' <- closureConvert tf
  return $ IrIfZ tb' tt' tf'
closureConvert (Fix i fn fty vn ty tm) = do
  (_, fvars) <- get
  vname <- generateName vn
  fname <- generateName fn
  frname <- generateName "fr"
  let ttm = openN [frname, vname] tm
  traceM $ "Termino\n" ++ show ttm
  modify (\(k, vars) -> (k, vname : frname : vars))
  itm <- closureConvert ttm
  let cname = "closure" ++ fname
  let itm' = makeLet itm cname (frname : fvars) True
  traceM $ "itm:\n" ++ show itm
  traceM $ "itm':\n" ++ show itm'
  tell [IrFun fname [cname, vname] itm']
  return $ MkClosure fname (fmap IrVar $ fname : fvars)
closureConvert (Let _ name _ tn tm) = do
  vname <- generateName name
  let ttm = open vname tm
  modify (\(k, vars) -> (k, vname : vars))
  itn <- closureConvert tn
  itm <- closureConvert ttm
  return $ IrLet vname itn itm

runCC :: Int -> [Decl Term] -> [IrDecl]
runCC _ [] = []
runCC n (decl : xs) = case decl of
  DeclType {} -> runCC n xs
  DeclFun _ name ty tt ->
    let freevars = freeVars tt
        ((ir, (k, _)), xx) = runWriter $ runStateT (closureConvert tt) (n, freevars)
        y = runCC k xs
     in IrVal name ir : xx ++ y

compilaC :: [Decl Term] -> String
compilaC xs = ir2C $ IrDecls $ runCC 0 xs

cWrite :: String -> FilePath -> IO ()
cWrite cp filename = writeFile filename cp