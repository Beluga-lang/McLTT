%token <string> VAR
%token <int> INT
%token EOF
%token ZERO
%token LAMBDA
%token DOT
%token COLON
%token SUCC
%token SPACE
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
  | NAT { Nat }
  | ZERO { Zero }
  | SUCC; o = obj { Succ o }
  | TYPE; SPACE; i = INT { Type i }
  | LPAREN; o = obj; RPAREN { o }
  | x = VAR { Var x }
  | LAMBDA; SPACE; x = VAR; DOT; o = obj { Fun (x, o) }
  | m = obj; SPACE; n = obj { App (m, n) }
  ;
