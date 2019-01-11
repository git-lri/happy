module ProduceSMLCode where

import Grammar
import Target                 ( Target(..) )
import GenUtils               ( mapDollarDollar, str, char, nl, strspace,
                                interleave, interleave', maybestr,
                                brack, brack' )
import qualified ProduceCode as PC

import Data.Array.ST          ( STUArray )
import Data.Array.Unboxed     ( UArray )
import Data.Array.MArray
import Data.Array.IArray
import Data.Char (ord)
import Data.Function
import qualified Data.Generics as G
import Data.List              ( groupBy, intercalate )
import qualified Data.List.Unique as U

import qualified Language.Haskell.Exts.Parser as P
import qualified Language.Haskell.Exts.Syntax as S
import qualified Numeric

produceParser :: Grammar                      -- grammar info
              -> ActionTable                  -- action table
              -> GotoTable                    -- goto table
              -> String                       -- stuff to go at the top
              -> Maybe String                 -- module header
              -> Maybe String                 -- module trailer
              -> Target                       -- type of code required
              -> Bool                         -- use coercions
              -> Bool                         -- use ghc extensions
              -> Bool                         -- strict parser
              -> String
produceParser (Grammar
              { productions = prods
              , non_terminals = nonterms
              , terminals = terms
              , types = nt_types
              , first_nonterm = first_nonterm'
              , eof_term = eof_term
              , first_term = fst_term
              , token_names = token_names0
              , lexer = lexer'
              , imported_identity = imported_identity'
              , monad = (use_monad,monad_context,monad_tycon,monad_then,monad_return)
              , token_specs = token_rep
              , token_type = token_type'
              , starts = starts'
              , error_handler = error_handler'
              , error_sig = error_sig'
              , attributetype = attributetype'
              , attributes = attributes'
              })
              action goto top_options module_header module_trailer
              target coerce ghc strict
    = ( str "%%\n"
      . str ("%name " ++ "StrictC"{- FIXME: not yet generic -} ++ "\n")
      . str ("%arg (source) : " ++ "SourceFile.t"{- FIXME: not yet generic -} ++ "\n")
      . str "%nodefault\n\n"
      . str "%nonterm "
      . interleave' "\n       | " (map (\i -> str (token_names' ! i ++ " of " ++ case nt_types ! i of Just s -> to_sml_ty s)) $ drop n_starts nonterms)
      . nl . nl
      . str "%term "
      . interleave' "\n    | " (let l = map (\i -> let n = token_names' ! i in (n, case lookup n [("ident", "ident"), ("tyident", "ident")] of Nothing -> Just "string"; x -> x)) terms in
                                map (\(n, type_n) -> str (n ++ case type_n of Just s -> " of " ++ s ; Nothing -> ""))
                                    (case l of (x, _) : xs -> (x, Nothing) : init xs ++ [(fst (last xs), Nothing)]))
      . nl . nl
      . str ("%eop " ++ token_names' ! eof_term)
      . nl
      . str ("%pos " ++ "SourcePos.t"{- FIXME: not yet generic -} ++ "\n")
      . str "%%"
      . nl . nl
      . str "(* production *)\n"
      . interleave "\n\n"
          (map (\(x@(n, _, _, _):xs) ->
                 let f n' (_, l, (code, var), No) =
                       n'
                       ++ (intercalate " " $ map (\i -> token_names' ! i) l)
                       ++ " ("
                       ++ show_code
                            (let var' = U.sortUniq var in
                             if var' == [] then id
                             else
                               \e ->
                                 G.everywhere (G.mkT replace_curry) e
                                 & S.Lambda () (map (\i -> S.PVar () (S.Ident () (PC.mkHappyVar i ""))) var')
                                 & S.Paren ()
                                 & \e -> foldl (\e i -> S.App () e (S.Var () (S.UnQual () (S.Ident () (token_names' ! (l !! (i - 1))))))) e var')
                            code
                       ++ ")"
                     name = token_names' ! n in
                 str $ name ++ " : " ++ f "" x ++ (concat . map (f ("\n" ++ replicate (length name) ' ' ++ " | "))) xs)
               $ groupBy (\(a1, _, _, _) (a2, _, _, _) -> a1 == a2)
               $ drop n_starts prods)
      . nl
      ) ""
  where
    n_starts = length starts'
    show_code f code =
      let to_sml = to_sml_exp f in
      case code of
        '%':'%':code1 -> to_sml code1 ++ "(* %% *)"
        '%':'^':code1 -> to_sml code1 ++ "(* %^ *)"
        '%':code1     -> to_sml_exp (S.App () (S.Var () (S.UnQual () (S.Ident () "wrap_monad"))) . S.Paren () . f) code1
        _ -> to_sml code
    token_names' =
      fmap (\body0 -> 
             let (l, body1) = f_span $ case body0 of ['\'',c,'\''] -> [c]
                                                     '"':s -> case reverse s of '"':s -> reverse s
                                                                                _ -> body0
                                                     _ -> body0
                 (r, body2) = f_span $ reverse body1
                 body3 = concat [conv l, conv_inter l body2, reverse body2, conv_inter body2 r, conv (reverse r)] in
             if body3 `elem` ["case", "do", "else", "for", "if", "struct", "while"] then
               body3 ++ "0"
             else
               body3)
           token_names0
    f_span = span (\x -> not (x >= 'a' && x <= 'z' || x >= 'A' && x <= 'Z'))
    conv = intercalate "_" . map (\x -> "x" ++ Numeric.showHex (ord x) "")
    conv_inter a b = if length a > 0 && length b > 0 then "_" else ""
    replace_curry :: S.Exp () -> S.Exp ()
    replace_curry e =
      case e of
        S.Case _ e0 l ->
          S.Case
            ()
            e0
            (map (\a -> case a of S.Alt _ (S.PApp _ (S.UnQual _ (S.Ident _ c)) l) rhs bind ->
                                    if c `elem` ["CDecl"] then
                                      S.Alt () (S.PApp () (S.UnQual () (S.Ident () (c ++ "0"))) [S.PTuple () S.Boxed l]) rhs bind
                                    else a
                                  _ -> a) l)
        S.App _ (S.App _ (S.Con _ (S.UnQual _ (S.Ident _ "CDecl"))) arg1) arg2@(S.List _ [S.Tuple _ _ _]) -> S.App () (S.App () (S.Con () (S.UnQual () (S.Ident () "CDecl_flat"))) arg1) arg2
        S.App _ (S.App _ (S.Con _ (S.UnQual _ (S.Ident _ "CDecl"))) arg1) (S.Paren _ (S.InfixApp _ arg2@(S.Tuple _ _ _) (S.QConOp _ (S.Special _ (S.Cons _))) arg3)) -> S.App () (S.App () (S.Con () (S.UnQual () (S.Ident () "CDecl"))) arg1) (S.Paren () (S.InfixApp () (S.Paren () (S.App () (S.Con () (S.UnQual () (S.Ident () "flat3"))) arg2)) (S.QConOp () (S.Special () (S.Cons ()))) arg3))
        _ -> e
    

--------------------------------------------------------------------------------

_Type t = case t of
  S.TyCon _ (S.UnQual _ (S.Ident _ e)) -> e
  S.TyCon _ (S.Special _ (S.UnitCon _)) -> "unit"
  S.TyFun loc t1 t2 -> "(" ++ _Type t1 ++ " -> " ++ _Type t2 ++ ")"
  S.TyTuple loc b l -> "(" ++ intercalate " * " (map _Type l) ++ ")"
  S.TyList loc t@(S.TyCon _ _) -> _Type t ++ " list"
  S.TyList loc t -> "(" ++ _Type t ++ ") list"
  S.TyApp loc t1@(S.TyCon _ _) t2@(S.TyCon _ _) -> _Type t2 ++ " " ++ _Type t1
  S.TyApp loc t1 t2 -> "(" ++ _Type t2 ++ ") " ++ _Type t1
  -- _ -> show t

_Exp e = case e of
  S.Var _ q -> _QName q
  S.Con _ q -> _QName q
  S.Lit _ l -> _Literal l
  S.InfixApp _ e1 (S.QVarOp _ (S.UnQual _ (S.Symbol _ "$"))) e2 -> _Exp (S.App () e1 (S.Paren () e2))
  S.InfixApp _ e1 (S.QVarOp _ (S.UnQual _ (S.Symbol _ "$!"))) e2 -> _Exp (S.App () e1 (S.Paren () e2))
  S.InfixApp _ e1 (S.QVarOp _ (S.UnQual _ (S.Symbol _ "."))) e2 -> _Exp e1 ++ " o " ++ _Exp e2
  S.InfixApp _ e1 (S.QVarOp _ (S.UnQual _ (S.Symbol _ "++"))) e2 -> _Exp e1 ++ " @ " ++ _Exp e2
  S.InfixApp _ e1 (S.QVarOp _ (S.UnQual _ (S.Symbol _ ">>"))) e2 -> _Exp e1 ++ " >> " ++ _Exp e2
  S.InfixApp _ e1 (S.QVarOp _ q@(S.UnQual _ (S.Ident _ _))) e2 -> _Exp (S.App () (S.App () (S.Var () q) e1) e2)
  S.InfixApp _ e1 (S.QConOp _ (S.Special _ (S.Cons _))) e2 -> _Exp e1 ++ " :: " ++ _Exp e2
  S.App _ e1 e2 -> _Exp e1 ++ " " ++ _Exp e2
  S.Lambda _ p e | all (\x -> case x of S.PVar _ _ -> True ; _ -> False) p -> concatMap (\x -> case x of S.PVar _ n -> "fn " ++ _Name n ++ " => ") p ++ _Exp e
  S.Let _ (S.BDecls _ l) e -> "let " ++ (intercalate "; " $ map (\x -> case x of S.PatBind _ (S.PVar _ (S.Ident _ s)) (S.UnGuardedRhs _ e) Nothing -> "val " ++ s ++ " = " ++ _Exp e) l) ++ " in " ++ _Exp e ++ " end"
  S.Case _ e l ->
    "case " ++ _Exp e ++ " of "
    ++ (intercalate " | " $ map (\x -> case x of S.Alt _ pat (S.UnGuardedRhs _ e) Nothing -> _Pat pat ++ " => " ++ _Exp e) l)
  S.Do _ l -> case reverse l of S.Qualifier _ x : xs -> foldl (\body p -> let (p', e) = case p of S.Generator _ p e -> (p, e) ; S.Qualifier _ e -> (S.PWildCard (), e) in "bind (" ++ _Exp e ++ ") (fn " ++ _Pat p' ++ " => " ++ body ++ ")") (_Exp x) xs
  S.Tuple _ _ l -> "(" ++ (intercalate ", " $ map _Exp l) ++ ")"
  S.List _ l -> "[" ++ (intercalate "; " $ map _Exp l) ++ "]"
  S.Paren _ e -> "(" ++ _Exp e ++ ")"
  S.LeftSection _ e (S.QVarOp _ q@(S.UnQual _ (S.Ident _ _))) -> _Exp (S.App () (S.Var () q) e)
  -- _ -> show e

_Pat p = case p of
  S.PVar _ n -> _Name n
  S.PInfixApp _ p1 (S.Special _ (S.Cons _)) p2 -> _Pat p1 ++ " :: " ++ _Pat p2
  S.PApp _ pe pl -> _QName pe ++ concatMap (\x -> " " ++ _Pat x) pl
  S.PTuple _ _ l -> "(" ++ (intercalate "," $ map _Pat l) ++ ")"
  S.PList () [] -> "[]"
  S.PParen _ p -> "(" ++ _Pat p ++ ")"
  S.PWildCard _ -> "_"
  -- _ -> show p

_Literal l = case l of
  S.String _ _ s -> "\"" ++ s ++ "\""
  S.Int _ _ s -> s
  -- _ -> show l

_QName q = case q of
  S.Qual _ (S.ModuleName _ s) n -> s ++ "." ++ _Name n
  S.UnQual _ n -> _Name n
  -- _ -> show q

_Name n = case n of
  S.Ident _ s -> s
  -- _ -> show n

to_sml_ty s = case P.parseType s of P.ParseOk t -> _Type t
to_sml_exp f s = case P.parseExp s of P.ParseOk t -> _Exp (f $ fmap (\_ -> ()) t)
