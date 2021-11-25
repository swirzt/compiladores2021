module C (ir2C) where

import Data.Text (unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal (renderStrict)
import IR
import Lang
import Debug.Trace
import Data.Maybe

ty2Doc :: Ty -> Doc a
ty2Doc NatTy = pretty "uint64_t"
ty2Doc (NameTy _ t) = ty2Doc t
ty2Doc (FunTy d c) = pretty "void**"

args2Doc :: [(Name, Maybe Ty)] -> [Doc a]
args2Doc [] = []
args2Doc ((n,Nothing):xs) = (pretty "void**" <+> name n) : args2Doc xs
args2Doc ((n,Just ty):xs) = (ty2Doc ty <+> name n) : args2Doc xs

decl2doc :: IrDecl -> Doc a
decl2doc (IrVal n t ty) = ty2Doc ty <+> name n <> semi
decl2doc (IrFun n args t ty) =
  let tyReturn = ty2Doc (tcodom ty) in
   tyReturn <+> name n <+> tupled (args2Doc args)
    <+> braces (nest 2 (line <> pretty "return" <+> ir2doc t <> semi) <> line)

fd4Main :: [IrDecl] -> Doc a
fd4Main xs =
  pretty "uint64_t fd4main()"
    <+> braces (nest 2 (line <> vsep (vals2doc xs ++ [pretty "return 0;"])) <> line)
  where
    vals2doc :: [IrDecl] -> [Doc a]
    vals2doc [] = []
    vals2doc [IrVal n t ty] = [name n <+> pretty "=" <+> ir2doc t <> semi, irPrintN (name n), semi]
    vals2doc (IrVal n t ty : ds) = (name n <+> pretty "=" <+>  ir2doc t <> semi) : vals2doc ds
    vals2doc (_ : ds) = vals2doc ds

name :: String -> Doc a
name n = pretty $ "fd4_" ++ n --prefijo fd4 para evitar colision con nombres de C.

stmt :: Doc a -> Doc a
stmt x = parens (braces (nest 2 (line <> x <> semi) <> line))

stmts :: [Doc a] -> Doc a
stmts xs =
  parens $
    braces $
      foldr (\x ds -> nest 2 (line <> x <> semi) <> ds) line xs

u64 :: Doc a
u64 = parens (pretty "uint64_t")

voidptr :: Doc a
voidptr = parens (pretty "void *")

argsTy2Doc :: [(Ir, Maybe Ty)] -> [Doc a]
argsTy2Doc [] = []
argsTy2Doc ((_,Nothing):xs) = (pretty "void**") : argsTy2Doc xs
argsTy2Doc ((_,Just ty):xs) = (ty2Doc ty) : argsTy2Doc xs

returnF :: Ty -> Ty -> Doc a
returnF NatTy NatTy = pretty "int_int"
returnF NatTy (FunTy _ _) = pretty "int_void"
returnF (FunTy _ _) (FunTy _ _) = pretty "void_void"
returnF (FunTy _ _) NatTy = pretty "void_int"
returnF (NameTy _ t) x = returnF t x
returnF x (NameTy _ t) = returnF x t

ir2doc :: Ir -> Doc a
ir2doc (IrVar n) = name n
ir2doc (IrGlobal n) = name n
ir2doc (IrCall f args dom codom) = parens (returnF codom (fromJust (snd (args!!1))) <+> ir2doc f) <> tupled (map (\(ir,_) -> ir2doc ir) args)
ir2doc (IrConst (CNat n)) = pretty n
ir2doc (IrBinaryOp Add a b) = ir2doc a <+> pretty "+" <+> ir2doc b
ir2doc (IrBinaryOp Sub a b) = pretty "fd4_sub" <> tupled [ir2doc a, ir2doc b]
ir2doc (IrLet n t t' tyL ty) = stmts [hsep [ty2Doc tyL, name n, pretty "=", ir2doc t] <> semi <> line <> ir2doc t']
ir2doc (IrIfZ c a b ty) = sep [ir2doc c, nest 2 (pretty "?" <+> ir2doc b), nest 2 (colon <+> ir2doc a)]
ir2doc (IrPrint str t) = stmts [pretty "wprintf" <> parens (pretty "L" <> pretty (show str)), irPrintN (ir2doc t)]
ir2doc (MkClosure f args ty) = pretty "fd4_mkclosure" <> tupled (name f : pretty (length args) : map ir2doc args)
ir2doc (IrAccess t i) = parens (ir2doc t) <> brackets (pretty i)

op2doc :: BinaryOp -> Doc a
op2doc Add = pretty "+"
op2doc Sub = pretty "-"

prelude :: Doc a
prelude =
  pretty "#include <inttypes.h>"
    <> line
    <> pretty "#include <wchar.h>"
    <> line
    <> pretty "#define int_int (uint64_t (*) (void**, uint64_t))"
    <> line
    <> pretty "#define int_void (uint64_t (*) (void**, void**))"
    <> line
    <> pretty "#define void_int (void** (*) (void**, uint64_t))"
    <> line
    <> pretty "#define void_void (void** (*) (void**, void**))"
    <> line
    <> pretty "extern void *fd4_mkclosure(void*, int, ...);"
    <> line
    <> pretty "extern uint64_t fd4_printn(uint64_t);"
    <> line
    <> pretty "extern uint64_t fd4_sub(uint64_t, uint64_t);"
    <> line

   

irPrintN :: Doc a -> Doc a
irPrintN x = pretty "fd4_printn" <> parens x

ir2C :: IrDecls -> String
ir2C (IrDecls xs) = unpack . renderStrict . layoutSmart defaultLayoutOptions $ vsep (prelude : mempty : map decl2doc xs ++ [mempty, mempty, fd4Main xs])