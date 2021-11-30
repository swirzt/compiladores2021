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
generateName :: Name -> StateT (Int, [(Name, Ty)]) (Writer [IrDecl]) Name
generateName n = do
  (k, _) <- get
  modify (\(h, vars) -> (h + 1, vars))
  return $ n ++ show k

makeLet :: Ir -> Name -> [(Name, Ty)] -> Bool -> Ty -> Ir
makeLet tm name xs False t = foldr (\((x, ty), y) r -> IrLet x (IrAccess (IrVar name) y) r ty t) tm (zip xs [1 ..])
makeLet tm _ [] True _ = tm
makeLet tm name ((x, ty) : xs) True t = IrLet x (IrVar name) (makeLet tm name xs False t) ty t

closureConvert :: TTerm -> StateT (Int, [(Name, Ty)]) (Writer [IrDecl]) Ir
closureConvert (TV var ty) = case var of
  Free name -> return $ IrVar name
  Global name -> return $ IrGlobal name
  Bound n -> undefined
closureConvert (TConst var ty) = return $ IrConst var
closureConvert (TLam name tv tm ty) = do
  (_, fvars) <- get
  vname <- generateName name -- Le damos un nombre unico a la variable ligada
  let ttm = openTTerm vname tm -- La abrimos
  modify (\(k, vars) -> (k, (vname, tv) : vars))
  itm <- closureConvert ttm -- hacemos la clausura del termino
  fname <- generateName "f" -- nombre unico para la funcion
  let cname = "closure" ++ fname -- nombre unico para la clausura
  let itm' = makeLet itm cname fvars False ty -- fijamos el acceso a variables libres
  tell [IrFun fname [(cname, Nothing), (vname, Just tv)] itm' ty] -- guardamos la declaracion top-level
  let (names, _) = unzip fvars
  return $ MkClosure fname (fmap IrVar names) ty -- retornamos el makeClosure
closureConvert (TApp tm1 tm2 tyDom tyCod) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  fname <- generateName "t"
  let newdef = IrVar fname
  return $ IrLet fname itm1 (IrCall (IrAccess newdef 0) [(newdef, Nothing), (itm2, Just tyDom)] tyDom tyCod) (FunTy tyDom tyCod) tyCod
closureConvert (TPrint str tm ty) = do
  itm <- closureConvert tm
  pname <- generateName "p"
  return $ IrLet pname itm (IrPrint str (IrVar pname)) ty ty
closureConvert (TBinaryOp bop tm1 tm2 ty) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  return $ IrBinaryOp bop itm1 itm2
closureConvert (TIfZ tb tt tf ty) = do
  tb' <- closureConvert tb
  tt' <- closureConvert tt
  tf' <- closureConvert tf
  return $ IrIfZ tb' tt' tf' ty
closureConvert (TFix fn tf vn tv tm ty) = do
  (_, fvars) <- get
  vname <- generateName vn
  fname <- generateName fn
  frname <- generateName "fr"
  let ttm = openNTTerm [frname, vname] tm
  modify (\(k, vars) -> (k, (vname, tv) : (frname, tf) : vars))
  itm <- closureConvert ttm
  let cname = "closure" ++ fname
  let itm' = makeLet itm cname ((frname, tf) : fvars) True ty
  tell [IrFun fname [(cname, Nothing), (vname, Just tv)] itm' ty]
  let (names, _) = unzip fvars
  return $ MkClosure fname (fmap IrVar names) ty
closureConvert (TLet name tyDom tn tm tyCod) = do
  vname <- generateName name
  let ttm = openTTerm vname tm
  modify (\(k, vars) -> (k, (vname, tyDom) : vars))
  itn <- closureConvert tn
  itm <- closureConvert ttm
  return $ IrLet vname itn itm tyDom tyCod

runCC :: Int -> [Decl TTerm] -> [IrDecl]
runCC _ [] = []
runCC n (decl : xs) = case decl of
  DeclType _ name ty ->
    let y = runCC n xs
     in (IrType name ty) : y
  DeclFun _ name ty tt ->
    let freevars = freeVarsTTerm tt
        ((ir, (k, _)), xx) = runWriter $ runStateT (closureConvert tt) (n, freevars)
        y = runCC k xs
     in (IrVal name ir ty) : xx ++ y

compilaC :: [Decl TTerm] -> String
compilaC xs = ir2C $ IrDecls $ runCC 0 xs

cWrite :: String -> FilePath -> IO ()
cWrite cp filename = writeFile filename cp