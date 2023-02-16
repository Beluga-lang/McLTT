%token <string> VAR
%token <int> INT
%token EOF
%token ZERO
%token LAMBDA
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
  | LAMBDA; x = VAR; DOT; o = obj { Fun (x, o) }
  | m = obj; n = obj { App (m, n) }
  ;
