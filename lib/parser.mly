%token <string> VAR
%token <int> INT
%token EOF
%token ZERO
%token LAMBDA
%token PI
%token DOT
%token COLON
%token SUCC
%token NAT
%token TYPE

%token LPAREN
%token RPAREN

%start <Cst.obj> prog

%%

prog:
  | o = obj; EOF { o }
  ;

obj:
  | LPAREN; o = obj; RPAREN { o }
  | NAT { Nat }
  | ZERO { Zero }
  | SUCC; o = obj { Succ o }
  | TYPE; i = INT { Type i }
  | x = VAR { Var x }
  | LAMBDA; args = args_list; DOT; o = obj {
    List.fold_left (fun curr (a, t) -> Cst.Fun (a, t, curr)) o args
  }
  | PI; args = args_list; DOT; o = obj {
    List.fold_left (fun curr (a, t) -> Cst.Pi (a, t, curr)) o args
  }
  | m = obj; n = obj { App (m, n) }
  ;

(* Parse multiple arguments:
   Read more at https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
args_list:
  | (* empty *) { [] }
  | l = args_list; LPAREN; x = VAR; COLON; t = obj; RPAREN
    { (x, t) :: l }
  ;

