%{

From Coq Require Import List String.

From Mcltt Require Import Syntax.

%}

%token <string> VAR
%token <nat> INT
%token ZERO LAMBDA PI SUCC NAT TYPE (* keywords *)
%token LPAREN RPAREN DOT COLON EOF (* delimiters *)

%start <Cst.obj> prog
%type <Cst.obj> obj app_obj simpl_obj
%type <string * Cst.obj> args_obj
%type <list (string * Cst.obj)> args_list

%%

prog:
  | obj EOF { $1 }

obj:
  | LAMBDA args_list DOT obj {
      List.fold_left (fun acc arg => Cst.fn (fst arg) (snd arg) acc) $2 $4 
  }
  | PI args_list DOT obj {
      List.fold_left (fun acc arg => Cst.pi (fst arg) (snd arg) acc) $2 $4
  }
  | SUCC obj { Cst.succ $2 }
  (* Application is a special case, where we must avoid conflict by associativity: *)
  (* see https://github.com/utgwkk/lambda-chama/blob/master/parser.mly *)
  | app_obj { $1 }

args_list:
  (* Nonempty list of arguments *)
  | args_list args_obj { $2 :: $1 }
  | args_obj { [$1] }

(* (x : A) *)
args_obj:
  | LPAREN VAR COLON obj RPAREN { ($2, $4) }

(* M N *)
app_obj:
  (* simpl_obj prevents conflict by associativity *)
  | app_obj simpl_obj { Cst.app $1 $2 }
  | simpl_obj { $1 }

(* Either a variable or parentheses around a complex object *)
simpl_obj:
  | VAR { Cst.var $1 }
  | NAT { Cst.nat }
  | ZERO { Cst.zero }
  | TYPE INT { Cst.typ $2 }
  | LPAREN obj RPAREN { $2 }

