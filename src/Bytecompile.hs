{-# LANGUAGE PatternSynonyms #-}

-- |
-- Module      : Byecompile
-- Description : Compila a bytecode. Ejecuta bytecode.
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
--
-- Este módulo permite compilar módulos a la BVM. También provee una implementación de la BVM
-- para ejecutar bytecode.
module Bytecompile (Bytecode, runBC, bcWrite, bcRead, bytecompileModule) where

import Data.Binary (Binary (get, put), Word32, decode, encode)
import Data.Binary.Get (getWord32le, isEmpty)
import Data.Binary.Put (putWord32le)
import qualified Data.ByteString.Lazy as BS
import Data.Char
import Lang
import MonadFD4
import Subst

type Opcode = Int

type Bytecode = [Opcode]

newtype Bytecode32 = BC {un32 :: [Word32]}

data Val
  = I Int
  | Fun Env Bytecode
  | RA Env Bytecode

type Env = [Val]

type Stack = [Val]

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs

  get = go
    where
      go = do
        empty <- isEmpty
        if empty
          then return $ BC []
          else do
            x <- getWord32le
            BC xs <- go
            return $ BC (x : xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL = 0

pattern RETURN = 1

pattern CONST = 2

pattern ACCESS = 3

pattern FUNCTION = 4

pattern CALL = 5

pattern ADD = 6

pattern SUB = 7

pattern IFZ = 8

pattern FIX = 9

pattern STOP = 10

pattern SHIFT = 11

pattern DROP = 12

pattern PRINT = 13

pattern PRINTN = 14

pattern SKIP = 15

pattern TAILCALL = 16

bc :: MonadFD4 m => Term -> m Bytecode
bc (V _ (Bound i)) = return [ACCESS, i]
bc (Const _ (CNat n)) = return [CONST, n]
bc (Lam _ _ _ tm) = do
  ts <- bt tm
  let len = length ts
  return $ [FUNCTION, len] ++ ts
bc (App _ tm1 tm2) = do
  ts1 <- bc tm1
  ts2 <- bc tm2
  return $ ts1 ++ ts2 ++ [CALL]
bc (Print _ str tm) = do
  ts <- bc tm
  let itr = stringToUnicode str
  return $ ts ++ [PRINT] ++ itr ++ [NULL, PRINTN]
bc (BinaryOp _ op tm1 tm2) = do
  ts1 <- bc tm1
  ts2 <- bc tm2
  let x = parseOp op
  return $ ts1 ++ ts2 ++ [x]
  where
    parseOp Add = ADD
    parseOp Sub = SUB
bc (Fix _ _ _ _ _ tm) = do
  ts <- bt tm
  let len = length ts
  return $ [FUNCTION, len] ++ ts ++ [FIX]
bc (Let _ _ _ tm1 tm2) = do
  ts1 <- bc tm1
  ts2 <- bc tm2
  return $ ts1 ++ [SHIFT] ++ ts2 ++ [DROP]
bc (IfZ _ tmb tmt tmf) = do
  tsb <- bc tmb
  tst <- bc tmt
  tsf <- bc tmf
  let tLen = length tst + 2 -- Tengo que saltear el SKIP y el largo del False
  let fLen = length tsf
  return $ tsb ++ [IFZ, tLen] ++ tst ++ [SKIP, fLen] ++ tsf
bc (V _ (Free _)) = undefined
bc (V _ (Global _)) = undefined

bt :: MonadFD4 m => Term -> m Bytecode
bt (App _ tm1 tm2) = do
  ts1 <- bc tm1
  ts2 <- bc tm2
  return $ ts1 ++ ts2 ++ [TAILCALL]
bt (IfZ _ tmb tmt tmf) = do
  tsb <- bc tmb
  tst <- bt tmt
  tsf <- bt tmf
  let tLen = length tst
  return $ tsb ++ [IFZ, tLen] ++ tst ++ tsf
bt (Let _ _ _ tm1 tm2) = do
  ts1 <- bc tm1
  ts2 <- bt tm2
  return $ ts1 ++ [SHIFT] ++ ts2
bt t = do
  tt <- bc t
  return $ tt ++ [RETURN]

stringToUnicode :: String -> [Int]
stringToUnicode xs = map ord xs

type Module = [Decl Term]

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule xs = do
  tm <- declToLet xs
  ys <- bc tm
  return $ ys ++ [PRINTN, STOP]

-- Esto es un fold?
declToLet :: MonadFD4 m => Module -> m Term
declToLet [DeclFun _ _ _ body] = return $ global2Free body
declToLet (DeclFun pos name ty body : xs) = do
  tm <- declToLet xs
  let bodyf = global2Free body
  return $ Let pos name ty bodyf (close name tm)
declToLet _ = undefined -- Para calmar al linter

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------

-- * Ejecución de bytecode

---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = map fromIntegral <$> un32 <$> decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC xs = runBC' xs [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' (CONST : n : c) e s = runBC' c e (I n : s)
runBC' (ADD : c) e (I n : I m : s) = runBC' c e (I (m + n) : s)
runBC' (ADD : _) _ _ = failFD4 "Error al ejecutar ADD"
runBC' (SUB : c) e (I n : I m : s) =
  let k = max 0 (m - n)
   in runBC' c e (I k : s)
runBC' (SUB : _) _ _ = failFD4 "Error al ejecutar SUB"
runBC' (ACCESS : i : c) e s = runBC' c e (e !! i : s)
runBC' (CALL : c) e (v : Fun ef cf : s) = runBC' cf (v : ef) (RA e c : s)
runBC' (CALL : _) _ _ = failFD4 "Error al ejecutar CALL"
runBC' (FUNCTION : l : c) e s = runBC' (drop l c) e (Fun e (take l c) : s)
runBC' (RETURN : _) _ (v : (RA e c) : s) = runBC' c e (v : s)
runBC' (RETURN : _) _ _ = failFD4 "Error al ejecutar RETURN"
runBC' (SHIFT : c) e (v : s) = runBC' c (v : e) s
runBC' (DROP : c) (_ : e) s = runBC' c e s
runBC' (PRINTN : c) e st@(I n : _) = do
  printFD4 (show n)
  runBC' c e st
runBC' (PRINTN : _) _ _ = failFD4 "Error al ejecutar PRINTN"
runBC' (PRINT : c) e s = printStr c e s
runBC' (FIX : c) e (Fun _ cf : s) =
  let efix = Fun efix cf : e
   in runBC' c e (Fun efix cf : s)
runBC' (FIX : _) _ _ = failFD4 "Error al ejecutar FIX"
runBC' (STOP : _) _ _ = return ()
runBC' (IFZ : tLen : c) e (I n : s) =
  if n == 0
    then runBC' c e s
    else runBC' (drop tLen c) e s
runBC' (IFZ : _) _ _ = failFD4 "Error al ejecutar IFZ"
runBC' (SKIP : len : c) e s = runBC' (drop len c) e s
runBC' (TAILCALL : _) _ (v : Fun ef cf : s) = runBC' cf (v : ef) s
runBC' (TAILCALL : _) _ _ = failFD4 "Error al ejecutar TAILCALL"
runBC' _ _ _ = failFD4 "Pasaron cosas"

printStr :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
printStr (NULL : c) e s = runBC' c e s
printStr (char : c) e s = do
  printFD4Char (chr char)
  printStr c e s
printStr _ _ _ = failFD4 "Error al desarmar la cadena"