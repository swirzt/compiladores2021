module ClosureConvert where

import C
import Control.Monad.State
import Control.Monad.Writer
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

makeLet :: Ir -> Name -> [(Name, Ty)] -> Bool -> Ir
makeLet tm name xs False =
  foldr
    (\((x, ty), y) r -> IrLet x (IrAccess (IrVar name) y) r ty)
    tm
    (zip xs [1 ..])
makeLet tm _ [] True = tm
makeLet tm name ((x, ty) : xs) True =
  IrLet x (IrVar name) (makeLet tm name xs False) ty

closureConvert :: TTerm -> StateT (Int, [(Name, Ty)]) (Writer [IrDecl]) Ir
closureConvert (V _ var) = case var of
  Free name -> return $ IrVar name
  Global name -> return $ IrGlobal name
  Bound _ -> undefined
closureConvert (Const _ var) = return $ IrConst var
closureConvert (Lam ty name tv tm) = do
  (_, fvars) <- get
  vname <- generateName name -- Le damos un nombre unico a la variable ligada
  let ttm = open vname tm -- La abrimos
  modify (\(k, vars) -> (k, (vname, tv) : vars))
  itm <- closureConvert ttm -- hacemos la clausura del termino
  fname <- generateName "f" -- nombre unico para la funcion
  let cname = "closure" ++ fname -- nombre unico para la clausura
  let itm' = makeLet itm cname fvars False -- fijamos el acceso a variables libres
  tell [IrFun fname [(cname, Nothing), (vname, Just tv)] itm' ty] -- guardamos la declaracion top-level
  let (names, _) = unzip fvars
  return $ MkClosure fname (fmap IrVar names) -- retornamos el makeClosure
closureConvert (App ty tm1 tm2) = do
  let ttdom (NameTy _ t) = ttdom t
      ttdom t = tdom t
      ttcodom (NameTy _ t) = ttcodom t
      ttcodom t = tcodom t
      tyDom = ttdom ty
      tyCod = ttcodom ty
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  fname <- generateName "t"
  let newdef = IrVar fname
  return $
    IrLet
      fname
      itm1
      (IrCall (IrAccess newdef 0) [(newdef, Nothing), (itm2, Just tyDom)] tyCod)
      (FunTy tyDom tyCod)
closureConvert (Print ty str tm) = do
  itm <- closureConvert tm
  pname <- generateName "p"
  return $ IrLet pname itm (IrPrint str (IrVar pname)) ty
closureConvert (BinaryOp _ bop tm1 tm2) = do
  itm1 <- closureConvert tm1
  itm2 <- closureConvert tm2
  return $ IrBinaryOp bop itm1 itm2
closureConvert (IfZ _ tb tt tf) = do
  tb' <- closureConvert tb
  tt' <- closureConvert tt
  tf' <- closureConvert tf
  return $ IrIfZ tb' tt' tf'
closureConvert (Fix ty fn tf vn tv tm) = do
  (_, fvars) <- get
  vname <- generateName vn
  fname <- generateName fn
  frname <- generateName "fr"
  let ttm = openN [frname, vname] tm
  modify (\(k, vars) -> (k, (vname, tv) : (frname, tf) : vars))
  itm <- closureConvert ttm
  let cname = "closure" ++ fname
  let itm' = makeLet itm cname ((frname, tf) : fvars) True
  tell [IrFun fname [(cname, Nothing), (vname, Just tv)] itm' ty]
  let (names, _) = unzip fvars
  return $ MkClosure fname (fmap IrVar names)
closureConvert (Let _ name tyDom tn tm) = do
  vname <- generateName name
  let ttm = open vname tm
  modify (\(k, vars) -> (k, (vname, tyDom) : vars))
  itn <- closureConvert tn
  itm <- closureConvert ttm
  return $ IrLet vname itn itm tyDom

runCC :: Int -> [Decl TTerm] -> [IrDecl]
runCC _ [] = []
runCC n (decl : xs) = case decl of
  DeclType _ name ty ->
    let y = runCC n xs
     in (IrType name ty) : y
  DeclFun _ name ty tt ->
    let freevars = freeVarsInfo tt
        ((ir, (k, _)), xx) =
          runWriter $
            runStateT (closureConvert tt) (n, freevars)
        y = runCC k xs
     in (IrVal name ir ty) : xx ++ y

compilaC :: [Decl TTerm] -> String
compilaC xs = ir2C $ IrDecls $ runCC 0 xs

cWrite :: String -> FilePath -> IO ()
cWrite cp filename = writeFile filename cp