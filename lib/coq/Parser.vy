%{

Require Import String.
Require Import List.

Module Cst.
Inductive obj :=
  | TType : nat -> obj
  | Nat : obj
  | Zero : obj
  | Succ : obj -> obj
  | App : obj -> obj -> obj
  | Fun : string -> obj -> obj -> obj
  | Pi : string -> obj -> obj -> obj
  | Var : string -> obj.
End Cst.

%}

%token <string> VAR
%token <nat> INT
%token ZERO LAMBDA PI SUCC NAT TYPE
%token LPAREN RPAREN DOT COLON EOF

%start <Cst.obj> prog
%type <Cst.obj> obj
%type <list (string * Cst.obj)> args_list
%type <list (string * Cst.obj)> rev_args_list
%type <string * Cst.obj> args_obj

%%

prog:
  | obj EOF { $1 }
  ;

obj:
  | LPAREN obj RPAREN { $2 }
  | NAT { Cst.Nat }
  | ZERO { Cst.Zero }
  | SUCC obj { Cst.Succ $2 }
  (* TODO: "Type" is a reserved keyword in Coq, which is why I've made it TType *)
  | TYPE INT { Cst.TType $2 }
  | VAR { Cst.Var $1 }
  | obj obj { Cst.App $1 $2 }
  (* Lambda with multiple arguments allowed with args_list *)
  | LAMBDA args_list DOT obj { List.fold_left (fun acc arg => Cst.Fun (fst arg) (snd arg) acc) $2 $4 }
  (* Pi with multiple arguments allowed with args_list *)
  | PI args_list DOT obj { List.fold_left (fun acc arg => Cst.Pi (fst arg) (snd arg) acc) $2 $4 }
  ;

args_list:
  | rev_args_list { List.rev $1 }

rev_args_list:
  (* Nonempty list of arguments *)
  | rev_args_list args_obj { $2 :: $1 }
  | args_obj { [$1] }

args_obj:
  LPAREN VAR COLON obj RPAREN { ($2, $4) };
