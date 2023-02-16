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
  | LAMBDA; LPAREN; x = VAR; COLON; t = obj; RPAREN; DOT; o = obj { Fun (x, t, o) }
  | PI; LPAREN; x = VAR; COLON; t = obj; RPAREN; DOT; o = obj { Pi (x, t, o) }
  | m = obj; n = obj { App (m, n) }
  ;
