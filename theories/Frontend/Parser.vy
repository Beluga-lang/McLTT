%{

From Coq Require Import List Arith.PeanoNat String.

From Mcltt Require Import Syntax.

Parameter loc : Type.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO LET IN (* keywords *)
%token <loc> ARROW "->" AT "@" BAR "|" COLON ":" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" DOT "." EQ ":=" EOF (* symbols *)

%start <Cst.obj * Cst.obj> prog
%type <Cst.obj> obj app_obj atomic_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params
%type <string -> Cst.obj -> Cst.obj -> Cst.obj> fnbinder
%type <(string * Cst.obj) * Cst.obj> let_defn
%type <list ((string * Cst.obj) * Cst.obj)> let_defns

%on_error_reduce obj params app_obj atomic_obj

%%

let prog :=
  exp = obj; ":"; typ = obj; EOF; <>

let fnbinder :=
  | PI; { Cst.pi }
  | LAMBDA; { Cst.fn }

let obj :=
  | ~ = fnbinder; ~ = params; "->"; ~ = obj; { List.fold_left (fun acc arg => fnbinder (fst arg) (snd arg) acc) params obj }
  | ~ = app_obj; <>

  | REC; escr = obj; RETURN; mx = VAR; "."; em = obj;
    "|"; ZERO; "=>"; ez = obj;
    "|"; SUCC; sx = VAR; ","; sr = VAR; "=>"; ms = obj;
    END; { Cst.natrec escr (snd mx) em ez (snd sx) (snd sr) ms }
  | SUCC; ~ = obj; { Cst.succ obj }
  
  | LET; ds = let_defns; IN; body = obj; { List.fold_left (fun acc arg => Cst.app acc (snd arg)) (List.rev ds) (List.fold_left (fun acc arg => Cst.fn (fst (fst arg)) (snd (fst arg)) acc) ds body) }


let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | TYPE; "@"; n = INT; { Cst.typ (snd n) }

  | NAT; { Cst.nat }
  | ZERO; { Cst.zero }
  | n = INT; { nat_rect (fun _ => Cst.obj) Cst.zero (fun _ => Cst.succ) (snd n) }

  | x = VAR; { Cst.var (snd x) }

  | "("; ~ = obj; ")"; <>

(* Reversed nonempty list of parameters *)
let params :=
  | ~ = params; ~ = param; { param :: params }
  | ~ = param; { [param] }

(* (x : A) *)
let param :=
  | "("; x = VAR; ":"; ~ = obj; ")"; { (snd x, obj) }

(* Reversed nonempty list of definitions *)
let let_defns :=
  | ~ = let_defns; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

(* (x : A) := t *)
let let_defn :=
  | "("; ~ = param; ":="; ~ = obj; ")"; { (param, obj) }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
