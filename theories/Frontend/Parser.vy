%{

From Coq Require Import List Arith.PeanoNat String.

From Mcltt Require Import Syntax.

Parameter loc : Type.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO (* keywords *)
%token <loc> ARROW AT BAR COLON COMMA DARROW LPAREN RPAREN EOF (* symbols *)

%start <Cst.obj * Cst.obj> prog
%type <Cst.obj> obj app_obj simpl_obj
%type <string * Cst.obj> args_obj
%type <list (string * Cst.obj)> args_list

%%

prog:
  | obj COLON obj EOF { ($1, $3) }

obj:
  | LAMBDA args_list ARROW obj {
      List.fold_left (fun acc arg => Cst.fn (fst arg) (snd arg) acc) $2 $4 
  }
  | PI args_list ARROW obj {
      List.fold_left (fun acc arg => Cst.pi (fst arg) (snd arg) acc) $2 $4
  }
  | REC obj RETURN VAR ARROW obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END {
      Cst.natrec $2 (snd $4) $6 $10 (snd $13) (snd $15) $17
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
  | LPAREN VAR COLON obj RPAREN { (snd $2, $4) }

(* M N *)
app_obj:
  (* simpl_obj prevents conflict by associativity *)
  | app_obj simpl_obj { Cst.app $1 $2 }
  | simpl_obj { $1 }

(* Either a variable or parentheses around a complex object *)
simpl_obj:
  | VAR { Cst.var (snd $1) }
  | NAT { Cst.nat }
  | INT { nat_rect (fun _ => Cst.obj) Cst.zero (fun _ => Cst.succ) (snd $1) }
  | ZERO { Cst.zero }
  | TYPE AT INT { Cst.typ (snd $3) }
  | LPAREN obj RPAREN { $2 }

%%

Extract Constant loc => "Lexing.position * Lexing.position".
