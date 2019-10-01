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
import Data.Char (ord, toLower, digitToInt)
import Data.Function
import qualified Data.Generics as G
import Data.List              ( groupBy, intercalate, partition )
import qualified Data.List.Unique as U
import qualified Data.Map.Strict as Map

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
              , priorities_full = prios
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
    = ( str ("open " ++ struct_ast ++ " open C_Grammar_Rule_Lib"{- FIXME: not yet generic -})
      . nl . nl
      . str ("type " ++ start_happy_ml_ty ++ " = ")
      . str start_happy_ml_ty_expand
      . nl . nl
      . interleave' "\n"
           (let var_x = "x" in
             snd $ foldl
               (\((pat, nb), acc) _ ->
                 (("Right (" ++ pat ++ ")", nb + 1), str ("fun " ++ start_happy_ml_val ++ show nb ++ " (" ++ var_x ++ " : " ++ start_happy_ml_ty ++ ") = case " ++ var_x ++ " of " ++ pat ++ " => SOME " ++ var_x ++ " | _ => NONE") : acc))
               (("Left " ++ var_x, 1), [])
               starts')
      . nl . nl
      . str "%%\n"
      . str "%pure\n"
      . str ("%name " ++ "C_Grammar"{- FIXME: not yet generic -} ++ "\n")
      . str "%arg (_) : Header.arg\n"
      . str "%nodefault\n\n"
      . str "%nonterm "
      . interleave' "\n       | " (str (start_happy_ml_rule ++ " of " ++ start_happy_ml_ty_expand) : (map (\i -> str (token_names' ! i ++ " of " ++ get_nt_types i)) $ drop n_starts nonterms))
      . nl . nl
      . str "%term "
      . interleave' "\n    | " ((map (\(n, _, _, _) -> str (mk_start n)) $ starts')
                                ++ concatMap (\(s, prio) -> case prio of ([], _) -> [str s]; _ -> []) prios
                                ++ (let l = map (\i -> let n = token_names' ! i in (n, ty_term' n)) terms in
                                    map (\(n, type_n) -> str (n ++ case type_n of Just s -> " of " ++ s ; Nothing -> ""))
                                        (case l of (x, _) : xs -> (x, Nothing) : init xs ++ [(fst (last xs), Nothing)])))
      . nl . nl
      . interleave "\n" (map (\(s, (_, prio)) -> str $ case prio of No -> "" ; Prio None _ -> "%nonassoc " ++ s) prios)
      . nl . nl
      . str ("(* fun token_of_string error " ++ intercalate " " (map mk_ty $ U.sortUniq ("string" : map snd ty_term0)) ++ " a1 a2 = fn\n    ")
      . interleave' "\n    "
          (let l = map (\i -> let n = token_names' ! i in ((n, token_names0 ! i), ty_term n)) terms in
           init (tail l)
           & map (\x@((n, n0), type_n) ->
                   ( x
                   , if n == n0
                     then Nothing
                     else
                       case n0 of
                         ['\'',c,'\''] -> Just ("\""++ [c] ++ "\"")
                         '"':s -> case reverse s of
                                    '"':s' ->
                                      if any (\c -> c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z') s'
                                      then Nothing else Just n0
                                    _ -> Nothing
                         _ -> Nothing))
           & partition (\x -> snd x == Nothing)
           & (let f (((n, n0), type_n), x) =
                        let s_end = n ++ case type_n of Just s -> " (" ++ mk_ty s ++ ", a1, a2)"
                                                        Nothing -> " (a1, a2)" in
                        case x
                        of
                          Nothing -> "val " ++ escape_sml (concatMap (\c -> let c' = toLower c in if c' >= 'a' && c' <= 'z' || c' >= '0' && c' <= '9' then [c'] else []) n0) ++ " = " ++ s_end ++ ""
                          Just n0 -> "| " ++ n0 ++ " => " ++ s_end in
              \(l2, l1) -> map f l1 ++ ["| x => let "] ++ map f l2 ++ ["in case x of", "(* | _ => error end *)"])
           & map str)
      . str "\n*)"
      . nl . nl
      . str ("%eop " ++ token_names' ! eof_term)
      . nl
      . str ("%pos " ++ "Position.T" ++ "\n")
      . str "%%"
      . nl . nl
      . str "(* production *)\n"
      . str (start_happy_ml_rule ++ " : ")
      . interleave' "\n            | " (reverse $ snd $ foldl
                                            (\ (acc_s, acc) (n, _, i, _) ->
                                              let n' = token_names' ! i in
                                              ("Right o " ++ acc_s, str (mk_start n ++ " " ++ n' ++ " ((" ++ acc_s ++ ") " ++ n' ++ "1)") : acc))
                                              ("Left", [])
                                              starts')
      . nl . nl
      . interleave "\n\n"
          (map (\(x@(n, _, _, _):xs) ->
                 let f n' (_, l, (code, var), prio) =
                       let l' = let (l'', _) = foldl (\(l', l_name) i ->
                                                       let name = token_names' ! i
                                                           name' = case Map.lookup name l_name of Nothing -> 1 ; Just x -> x + 1 in
                                                       ((name ++ show name') : l', Map.insert name name' l_name))
                                                     ([], Map.empty)
                                                     l in
                                reverse l'' in
                       n'
                       ++ (intercalate " " $ map (\i -> token_names' ! i) l)
                       ++ (case prio of (Nothing, _) -> "" ; (Just s, _) -> " %prec " ++ s)
                       ++ " ("
                       ++ show_code
                            (\e ->
                              G.everywhere (G.mkT replace_curry) e
                              & let var' = U.sortUniq var in
                                if var' == [] then id
                                else
                                  \e ->
                                    e
                                    & S.Lambda () (map (\i -> S.PVar () (S.Ident () (PC.mkHappyVar i ""))) var')
                                    & S.Paren ()
                                    & \e -> foldl (\e i -> S.App () e (S.Var () (S.UnQual () (S.Ident () (l' !! (i - 1))))))
                                                  e
                                                  var'
                              & let l_class_fun = U.sortUniq (G.everything (++) (G.mkQ [] find_class_fun) e) in
                                case l_class_fun of
                                [] -> id
                                _ ->
                                  \e ->
                                    e
                                    & S.Lambda () (map (\(n, _, _) -> S.PVar () (S.Ident () n)) l_class_fun)
                                    & S.Paren ()
                                    & \e -> foldl (\e (n, i, (pat, n')) ->
                                                    let name = l' !! (i - 1) in
                                                    S.App () e ((S.Paren () (S.Lambda () pat (S.App () n' (S.Lit () (S.Int () (fromIntegral (i - 1)) (show (i - 1)))))))))
                                                  e
                                                  l_class_fun)
                            code
                       ++ ")"
                     name = token_names' ! n in
                 str $ name ++ " : " ++ f "" x ++ (concat . map (f ("\n" ++ replicate (length name) ' ' ++ " | "))) xs)
               $ groupBy (\(a1, _, _, _) (a2, _, _, _) -> a1 == a2)
               $ drop n_starts prods)
      . nl
      ) ""
  where
    struct_ast = "C_Ast"{- FIXME: not yet generic -}
    ty_term0 = [("cchar", "cChar"), ("cint", "cInteger"), ("cfloat", "cFloat"), ("cstr", "cString"), ("ident", "ident"), ("tyident", "ident"), ("clangcversion", "ClangCVersion")]
    ty_term n = case lookup n ty_term0 of Nothing -> Just "string"; x -> x
    ty_term' = let ty_term0' = map (\(s1, s2) -> (s1, struct_ast ++ "." ++ s2)) ty_term0 in \n -> case lookup n ty_term0' of Nothing -> Just "string"; x -> x
    mk_ty s = "ty_" ++ s
    mk_start s = "start_" ++ s
    start_happy_ml_ty = "start_happy"
    start_happy_ml_val = "start_happy"
    start_happy_ml_rule = "start_happy"
    start_happy_ml_ty_expand =
      foldl (\acc (_, _, i, _) -> ("(" ++ get_nt_types i ++ ", " ++ acc ++ ") either")) "unit" (reverse starts')
    get_nt_types i = case nt_types ! i of Just s -> to_sml_ty s
    n_starts = length starts'
    show_code f code =
      let to_sml = fst . to_sml_exp f in
      case code of
        '%':'%':code1 -> "(*%%*)" ++ to_sml code1
        '%':'^':code1 -> "(*%^*)" ++ to_sml code1
        '%':code1     -> "(*%*)" ++ to_sml code1
        _ -> case to_sml_exp f code of (code, True) -> "(*%*)" ++ code
                                       (code, False) -> code
    token_names' =
      fmap (\body0 -> 
             let (l, body1) = f_span $ case body0 of ['\'',c,'\''] -> [c]
                                                     '"':s -> case reverse s of '"':s -> reverse s
                                                                                _ -> body0
                                                     _ -> body0
                 (r, body2) = f_span $ reverse body1
                 body3 = concat [conv l, conv_inter l body2, reverse body2, conv_inter body2 r, conv (reverse r)] in
             escape_sml body3)
           token_names0
    escape_sml body3 =
             if body3 `elem` ["case", "do", "else", "for", "if", "struct", "while", "return"] then
               body3 ++ "0"
             else
               body3
    f_span = span (\x -> not (x >= 'a' && x <= 'z' || x >= 'A' && x <= 'Z'))
    conv = intercalate "_" . map (\x -> "x" ++ Numeric.showHex (ord x) "")
    conv_inter a b = if length a > 0 && length b > 0 then "_" else ""
    replace_curry :: S.Exp () -> S.Exp ()
    replace_curry e =
      case e of
        S.Case _ (S.Var _ (S.UnQual _ i@(S.Ident _ _))) [S.Alt _ (S.PApp _ (S.UnQual _ (S.Ident _ c)) [S.PWildCard _, v]) (S.UnGuardedRhs _ f) Nothing] | c `elem` ["CTokILit", "CTokCLit", "CTokFLit", "CTokSLit"] ->
          S.App () (S.App () (S.Con () (S.UnQual () (S.Ident () c))) (S.Var () (S.UnQual () i))) (S.Paren () (S.Lambda () [v] f))
        S.Case _ e0 l ->
          S.Case
            ()
            e0
            (map (\a -> case a of S.Alt _ (S.PApp _ (S.UnQual _ (S.Ident _ c)) l) rhs bind ->
                                    if c `elem` ["CDecl"] then
                                      S.Alt () (S.PApp () (S.UnQual () (S.Ident () (c ++ "0"))) [S.PTuple () S.Boxed l]) rhs bind
                                    else
                                      S.Alt () (S.PApp () (S.UnQual () (S.Ident () (case lookup c [("Nothing", "None"), ("Just", "Some")] of Just x -> x ; Nothing -> c))) l) rhs bind
                                  S.Alt _ (S.PTuple _ S.Boxed [S.PApp _ (S.UnQual _ (S.Ident _ "Just")) l, pat]) rhs bind ->
                                    S.Alt () (S.PTuple () S.Boxed [S.PApp () (S.UnQual () (S.Ident () "Some")) (case l of [S.PParen _ (S.PApp _ (S.UnQual _ (S.Ident _ c0)) l0)] -> if c0 `elem` ["CDeclr"] then [S.PParen () (S.PApp () (S.UnQual () (S.Ident () (c0 ++ "0"))) [S.PTuple () S.Boxed l0])] else l ; _ -> l), pat]) rhs bind
                                  S.Alt _ (S.PTuple _ S.Boxed [S.PApp _ (S.UnQual _ (S.Ident _ "Nothing")) l, pat]) rhs bind ->
                                    S.Alt () (S.PTuple () S.Boxed [S.PApp () (S.UnQual () (S.Ident () "None")) l, pat]) rhs bind
                                  _ -> a) l)
        S.App _ (S.App _ (S.Con _ (S.UnQual _ (S.Ident _ "CDecl"))) arg1) arg2@(S.List _ [S.Tuple _ _ _]) -> S.App () (S.App () (S.Con () (S.UnQual () (S.Ident () "CDecl_flat"))) arg1) arg2
        S.App _ (S.App _ (S.Con _ (S.UnQual _ (S.Ident _ "CDecl"))) arg1) (S.Paren _ (S.InfixApp _ arg2@(S.Tuple _ _ _) (S.QConOp _ (S.Special _ (S.Cons _))) arg3)) -> S.App () (S.App () (S.Con () (S.UnQual () (S.Ident () "CDecl"))) arg1) (S.Paren () (S.InfixApp () (S.Paren () (S.App () (S.Con () (S.UnQual () (S.Ident () "flat3"))) arg2)) (S.QConOp () (S.Special () (S.Cons ()))) arg3))
        S.App _ (S.Var _ (S.UnQual _ (S.Ident _ "withNodeInfo"))) (S.Var _ (S.UnQual _ (S.Ident _ "d"))) -> S.App () (S.Var () (S.UnQual () (S.Ident () "withNodeInfo_CExtDecl"))) (S.Var () (S.UnQual () (S.Ident () "d")))
        S.App _ (S.Var _ (S.UnQual _ (S.Ident _ "withNodeInfo"))) (S.Var _ (S.UnQual _ (S.Ident _ "es"))) -> S.App () (S.Var () (S.UnQual () (S.Ident () "withNodeInfo_CExpr"))) (S.Var () (S.UnQual () (S.Ident () "es")))
        _ -> e

    find_class_fun0 name n =
      [(name, digitToInt n, ([S.PWildCard ()], S.Var () (S.UnQual () (S.Ident () name))))]
    find_class_fun1 name n =
      [( name
       , digitToInt n
       , let var_x = "x" in
         ( [S.PVar () (S.Ident () var_x), S.PWildCard ()]
         , S.App () (S.Con () (S.UnQual () (S.Ident () name))) (S.Var () (S.UnQual () (S.Ident () var_x)))))]
    find_class_fun e = case e of
      S.App () (S.Var () (S.UnQual () (S.Ident () "withNodeInfo"))) (S.Var () (S.UnQual () (S.Ident () var))) ->
        case var of
          'h' : 'a' : 'p' : 'p' : 'y' : '_' : 'v' : 'a' : 'r' : '_' : n : [] -> find_class_fun0 "withNodeInfo" n
          _ -> []
      S.App _ (S.Var _ (S.UnQual _ (S.Ident _ "withAttribute"))) (S.Var _ (S.UnQual _ (S.Ident _ var))) ->
        case var of
          'h' : 'a' : 'p' : 'p' : 'y' : '_' : 'v' : 'a' : 'r' : '_' : n : [] -> find_class_fun0 "withAttribute" n
          _ -> []
      S.App _ (S.Var _ (S.UnQual _ (S.Ident _ "withAttributePF"))) (S.Var _ (S.UnQual _ (S.Ident _ var))) ->
        case var of
          'h' : 'a' : 'p' : 'p' : 'y' : '_' : 'v' : 'a' : 'r' : '_' : n : [] -> find_class_fun0 "withAttributePF" n
          _ -> []
      S.App _ (S.App _ (S.Con _ (S.UnQual _ (S.Ident _ "L"))) (S.Con _ (S.UnQual _ (S.Ident _ _)))) (S.Paren _ (S.App _ (S.Var _ (S.UnQual _ (S.Ident _ "posOf"))) (S.Var _ (S.UnQual _ (S.Ident _ var))))) ->
        case var of
          'h' : 'a' : 'p' : 'p' : 'y' : '_' : 'v' : 'a' : 'r' : '_' : n : [] -> find_class_fun1 "L" n
          _ -> []
      _ -> []

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
  S.InfixApp _ e1 (S.QVarOp _ q@(S.UnQual _ (S.Ident _ _))) e2 -> _Exp (S.App () (S.App () (S.Var () q) (S.Paren () e1)) (S.Paren () e2))
  S.InfixApp _ e1 (S.QConOp _ (S.Special _ (S.Cons _))) e2 -> _Exp e1 ++ " :: " ++ _Exp e2
  S.App _ e1 e2 -> _Exp e1 ++ " " ++ _Exp e2
  S.Lambda _ p e | all (\x -> case x of S.PVar _ _ -> True ; S.PWildCard _ -> True ; _ -> False) p -> concatMap (\x -> "fn " ++ (case x of S.PVar _ n -> _Name n ; S.PWildCard _ -> "_") ++ " => ") p ++ _Exp e
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
  S.PTuple _ _ l -> "(" ++ (intercalate ", " $ map _Pat l) ++ ")"
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
  S.Special _ (S.UnitCon _) -> "()"
  -- _ -> show q

_Name n = case n of
  S.Ident _ s -> s
  -- _ -> show n

to_sml_ty s = case P.parseType s of P.ParseOk t -> _Type t
to_sml_exp f s = case P.parseExp s of
  P.ParseOk t ->
    let e = fmap (\_ -> ()) t in
    ( _Exp (f e)
    , case e of
        S.App _ (S.App _ (S.Con _ (S.UnQual _ (S.Ident _ "L"))) (S.Con _ (S.UnQual _ (S.Ident _ _)))) (S.Paren _ (S.App _ (S.Var _ (S.UnQual _ (S.Ident _ "posOf"))) (S.Var _ (S.UnQual _ (S.Ident _ _))))) -> True
        _ -> False)
