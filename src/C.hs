module C (ir2C) where

import Data.Text (unpack)
import IR
import Lang
import Prettyprinter
import Prettyprinter.Render.Terminal (renderStrict)

ty2Doc :: Ty -> Doc a
ty2Doc NatTy = pretty "nat"
ty2Doc (NameTy n _) = name n
ty2Doc (FunTy _ _) = pretty "clos"

args2Doc :: [(Name, Maybe Ty)] -> [Doc a]
args2Doc [] = []
args2Doc ((n, Nothing) : xs) = (pretty "clos" <+> name n) : args2Doc xs
args2Doc ((n, Just ty) : xs) = (ty2Doc ty <+> name n) : args2Doc xs

argsTy2Doc :: [(b, Maybe Ty)] -> [Doc a]
argsTy2Doc [] = []
argsTy2Doc ((_, Nothing) : xs) = (pretty "clos") : argsTy2Doc xs
argsTy2Doc ((_, Just ty) : xs) = (ty2Doc ty) : argsTy2Doc xs

decl2doc :: IrDecl -> Doc a
decl2doc (IrVal n _ ty) = ty2Doc ty <+> name n <> semi
decl2doc (IrFun n args t ty) =
  let tyReturn = ty2Doc (tcodom ty)
   in tyReturn <+> name n <+> tupled (args2Doc args)
        <+> braces (nest 2 (line <> pretty "return" <+> ir2doc t <> semi) <> line)
decl2doc (IrType n ty) = pretty "#define" <+> name n <+> ty2Doc ty

fd4Main :: [IrDecl] -> Doc a
fd4Main xs =
  pretty "nat fd4main()"
    <+> braces (nest 2 (line <> vsep (vals2doc xs ++ [pretty "return 0;"])) <> line)
  where
    vals2doc :: [IrDecl] -> [Doc a]
    vals2doc [] = []
    vals2doc [IrVal n t _] = [name n <+> pretty "=" <+> ir2doc t <> semi, irPrintN (name n), semi]
    vals2doc (IrVal n t _ : ds) = (name n <+> pretty "=" <+> ir2doc t <> semi) : vals2doc ds
    vals2doc (_ : ds) = vals2doc ds

name :: String -> Doc a
name n = pretty $ "fd4_" ++ n --prefijo fd4 para evitar colision con nombres de C.

stmts :: [Doc a] -> Doc a
stmts xs =
  parens $
    braces $
      foldr (\x ds -> nest 2 (line <> x <> semi) <> ds) line xs

ir2doc :: Ir -> Doc a
ir2doc (IrVar n) = name n
ir2doc (IrGlobal n) = name n
ir2doc (IrCall f args codomi) = parens (parens (ty2Doc codomi <+> pretty "(*)" <+> tupled (argsTy2Doc args)) <+> ir2doc f) <> tupled (map (\(ir, _) -> ir2doc ir) args)
ir2doc (IrConst (CNat n)) = pretty n
ir2doc (IrBinaryOp Add a b) = ir2doc a <+> pretty "+" <+> ir2doc b
ir2doc (IrBinaryOp Sub a b) = pretty "fd4_sub" <> tupled [ir2doc a, ir2doc b]
ir2doc (IrLet n t t' tyL) = stmts [hsep [ty2Doc tyL, name n, pretty "=", ir2doc t] <> semi <> line <> ir2doc t']
ir2doc (IrIfZ c a b) = sep [ir2doc c, nest 2 (pretty "?" <+> ir2doc b), nest 2 (colon <+> ir2doc a)]
ir2doc (IrPrint str t) = stmts [pretty "wprintf" <> parens (pretty "L" <> pretty (show str)), irPrintN (ir2doc t)]
ir2doc (MkClosure f args) = pretty "fd4_mkclosure" <> tupled (name f : pretty (length args) : map ir2doc args)
ir2doc (IrAccess t i) = ir2doc t <> brackets (pretty i)

prelude :: Doc a
prelude =
  pretty "#include <inttypes.h>"
    <> line
    <> pretty "#include <wchar.h>"
    <> line
    <> pretty "#define clos void**"
    <> line
    <> pretty "#define nat uint64_t"
    <> line
    <> pretty "extern clos fd4_mkclosure(void*, int, ...);"
    <> line
    <> pretty "extern nat fd4_printn(nat);"
    <> line
    <> pretty "extern nat fd4_sub(nat, nat);"
    <> line

irPrintN :: Doc a -> Doc a
irPrintN x = pretty "fd4_printn" <> parens x

ir2C :: IrDecls -> String
ir2C (IrDecls xs) = unpack . renderStrict . layoutSmart defaultLayoutOptions $ vsep (prelude : mempty : map decl2doc xs ++ [mempty, mempty, fd4Main xs])