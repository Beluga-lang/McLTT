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
    List.fold_right (fun (a, t) curr -> Cst.Fun (a, t, curr)) args o
  }
  | PI; args = args_list; DOT; o = obj {
    List.fold_right (fun (a, t) curr -> Cst.Pi (a, t, curr)) args o
  }
  | m = obj; n = obj { App (m, n) }
  ;

(* Parse multiple arguments in lambda:
   Read more at https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
args_list: l = rev_args_list { List.rev l };

rev_args_list:
  | (* empty *) { [] }
  | l = rev_args_list; LPAREN; x = VAR; COLON; t = obj; RPAREN
    { (x, t) :: l }
  ;

