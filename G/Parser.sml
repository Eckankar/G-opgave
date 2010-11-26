local
type t__1__ = (int*int)
type t__2__ = (int*int)
type t__3__ = (int*int)
type t__4__ = (int*int)
type t__5__ = (int*int)
type t__6__ = (int*int)
type t__7__ = (int*int)
type t__8__ = string*(int*int)
type t__9__ = (int*int)
type t__10__ = (int*int)
type t__11__ = (int*int)
type t__12__ = (int*int)
type t__13__ = int*(int*int)
type t__14__ = (int*int)
type t__15__ = (int*int)
type t__16__ = (int*int)
type t__17__ = (int*int)
in
datatype token =
    ARROW of t__1__
  | BAR of t__2__
  | BOOL of t__3__
  | COLON of t__4__
  | END of t__5__
  | EOF of t__6__
  | FUN of t__7__
  | ID of t__8__
  | INT of t__9__
  | LPAR of t__10__
  | MATCHARROW of t__11__
  | MINUS of t__12__
  | NUM of t__13__
  | PLUS of t__14__
  | READ of t__15__
  | RPAR of t__16__
  | WRITE of t__17__
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";

val yytransl = #[
  257 (* ARROW *),
  258 (* BAR *),
  259 (* BOOL *),
  260 (* COLON *),
  261 (* END *),
  262 (* EOF *),
  263 (* FUN *),
  264 (* ID *),
  265 (* INT *),
  266 (* LPAR *),
  267 (* MATCHARROW *),
  268 (* MINUS *),
  269 (* NUM *),
  270 (* PLUS *),
  271 (* READ *),
  272 (* RPAR *),
  273 (* WRITE *),
    0];

val yylhs = "\255\255\
\\001\000\006\000\006\000\002\000\005\000\005\000\004\000\004\000\
\\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\\000\000";

val yylen = "\002\000\
\\003\000\009\000\000\000\001\000\001\000\001\000\003\000\003\000\
\\001\000\001\000\003\000\003\000\002\000\001\000\002\000\003\000\
\\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\
\\009\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\001\000\000\000\000\000\004\000\000\000\016\000\000\000\000\000\
\\000\000\000\000\006\000\005\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\002\000\000\000";

val yydgoto = "\002\000\
\\004\000\021\000\012\000\029\000\030\000\005\000";

val yysindex = "\004\000\
\\002\255\000\000\008\255\000\000\052\255\020\255\052\255\052\255\
\\000\000\000\000\052\255\252\254\024\255\000\000\011\255\000\000\
\\000\000\052\255\052\255\000\000\019\255\000\000\000\000\000\000\
\\024\255\006\255\000\000\000\000\042\255\018\255\006\255\002\255\
\\052\255\035\255\000\000\043\255";

val yyrindex = "\000\000\
\\058\255\000\000\000\000\000\000\000\000\000\000\001\255\000\000\
\\000\000\000\000\000\000\000\000\000\000\016\255\000\000\029\255\
\\000\000\000\000\000\000\000\000\000\000\000\000\034\255\047\255\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\058\255\
\\000\000\033\255\000\000\049\255";

val yygindex = "\000\000\
\\000\000\017\000\249\255\025\000\000\000\026\000";

val YYTABLESIZE = 75;
val yytable = "\014\000\
\\015\000\017\000\010\000\016\000\001\000\010\000\010\000\018\000\
\\003\000\019\000\023\000\024\000\010\000\027\000\010\000\006\000\
\\010\000\013\000\028\000\025\000\013\000\013\000\018\000\013\000\
\\019\000\036\000\022\000\013\000\033\000\013\000\015\000\013\000\
\\020\000\015\000\015\000\012\000\031\000\008\000\012\000\012\000\
\\015\000\026\000\015\000\031\000\015\000\012\000\032\000\012\000\
\\011\000\012\000\007\000\011\000\011\000\007\000\018\000\034\000\
\\019\000\035\000\011\000\007\000\011\000\008\000\011\000\000\000\
\\009\000\003\000\010\000\003\000\011\000\000\000\003\000\000\000\
\\003\000\000\000\003\000";

val yycheck = "\007\000\
\\008\000\006\001\002\001\011\000\001\000\005\001\006\001\012\001\
\\007\001\014\001\018\000\019\000\012\001\008\001\014\001\008\001\
\\016\001\002\001\013\001\001\001\005\001\006\001\012\001\004\001\
\\014\001\033\000\016\001\012\001\011\001\014\001\002\001\016\001\
\\009\001\005\001\006\001\002\001\002\001\005\001\005\001\006\001\
\\012\001\025\000\014\001\002\001\016\001\012\001\005\001\014\001\
\\002\001\016\001\002\001\005\001\006\001\005\001\012\001\031\000\
\\014\001\032\000\012\001\008\001\014\001\010\001\016\001\255\255\
\\013\001\008\001\015\001\010\001\017\001\255\255\013\001\255\255\
\\015\001\255\255\017\001";

val yyact = vector_ 18 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 28 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 2 : Cat.FunDec list
val d__2__ = peekVal 1 : Cat.Exp
val d__3__ = peekVal 0 : (int*int)
in
( ([],(d__1__),(d__2__)) ) end : Cat.Prog))
;
(* Rule 2, file Parser.grm, line 32 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 8 : (int*int)
val d__2__ = peekVal 7 : string*(int*int)
val d__3__ = peekVal 6 : (int*int)
val d__4__ = peekVal 5 : Cat.Type
val d__5__ = peekVal 4 : (int*int)
val d__6__ = peekVal 3 : Cat.Type
val d__7__ = peekVal 2 : Cat.Match
val d__8__ = peekVal 1 : (int*int)
val d__9__ = peekVal 0 : Cat.FunDec list
in
( (#1 (d__2__), (d__4__), (d__6__), (d__7__), (d__1__)) :: (d__9__) ) end : Cat.FunDec list))
;
(* Rule 3, file Parser.grm, line 33 *)
val _ = update_ yyact 3
(fn () => repr(let
in
( [] ) end : Cat.FunDec list))
;
(* Rule 4, file Parser.grm, line 36 *)
val _ = update_ yyact 4
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Cat.Int (d__1__) ) end : Cat.Type))
;
(* Rule 5, file Parser.grm, line 39 *)
val _ = update_ yyact 5
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Cat.NumP (d__1__) ) end : Cat.Pat))
;
(* Rule 6, file Parser.grm, line 40 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Cat.VarP (d__1__) ) end : Cat.Pat))
;
(* Rule 7, file Parser.grm, line 44 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 2 : Cat.Pat
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Cat.Exp
in
( [((d__1__),(d__3__))] ) end : Cat.Match))
;
(* Rule 8, file Parser.grm, line 46 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 2 : Cat.Match
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Cat.Match
in
( (d__1__) @ (d__3__) ) end : Cat.Match))
;
(* Rule 9, file Parser.grm, line 49 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Cat.Num (d__1__) ) end : Cat.Exp))
;
(* Rule 10, file Parser.grm, line 50 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Cat.Var (d__1__) ) end : Cat.Exp))
;
(* Rule 11, file Parser.grm, line 51 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 2 : Cat.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Cat.Exp
in
( Cat.Plus ((d__1__), (d__3__), (d__2__)) ) end : Cat.Exp))
;
(* Rule 12, file Parser.grm, line 52 *)
val _ = update_ yyact 12
(fn () => repr(let
val d__1__ = peekVal 2 : Cat.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Cat.Exp
in
( Cat.Minus ((d__1__), (d__3__), (d__2__)) ) end : Cat.Exp))
;
(* Rule 13, file Parser.grm, line 54 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 1 : string*(int*int)
val d__2__ = peekVal 0 : Cat.Exp
in
( Cat.Apply (#1 (d__1__), (d__2__), #2 (d__1__)) ) end : Cat.Exp))
;
(* Rule 14, file Parser.grm, line 55 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Cat.Read (d__1__) ) end : Cat.Exp))
;
(* Rule 15, file Parser.grm, line 56 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Cat.Exp
in
( Cat.Write ((d__2__), (d__1__)) ) end : Cat.Exp))
;
(* Rule 16, file Parser.grm, line 57 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Cat.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Cat.Exp))
;
(* Entry Prog *)
val _ = update_ yyact 17 (fn () => raise yyexit (peekVal 0));
val yytables : parseTables =
  ( yyact,
    yytransl,
    yylhs,
    yylen,
    yydefred,
    yydgoto,
    yysindex,
    yyrindex,
    yygindex,
    YYTABLESIZE,
    yytable,
    yycheck );
fun Prog lexer lexbuf = yyparse yytables 1 lexer lexbuf;
