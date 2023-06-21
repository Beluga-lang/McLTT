Require Import String.
Require Import List.

(* CST term *)
Module Cst.
Inductive obj : Set :=
  | typ : nat -> obj
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | app : obj -> obj -> obj
  | fn : string -> obj -> obj -> obj
  | pi : string -> obj -> obj -> obj
  | var : string -> obj.
End Cst.

(* AST term *)
Inductive exp : Set :=
  (* Natural numbers *)
  | a_zero : exp
  | a_succ : exp -> exp
  (* Type constructors *)
  | a_nat : exp
  | a_typ : nat -> exp
  | a_var : nat -> exp
  (* Functions *)
  | a_fn : exp -> exp -> exp
  | a_app : exp -> exp -> exp
  | a_pi : exp -> exp -> exp
  | a_rec : exp -> exp -> exp -> exp -> exp
  (* Substitutions *)
  | a_sub : exp -> subst -> exp
with subst : Set :=
  | a_id : subst
  | a_weaken : subst
  | a_compose : subst -> subst -> subst
  | a_extend : subst -> exp -> subst.

Inductive Ne : Set :=
| ne_var : nat -> Ne
| ne_rec : Nf -> Nf -> Nf -> Ne -> Ne 
| ne_app : Ne -> Nf -> Ne
with Nf : Set :=
| nf_ne : Ne -> Nf
| nf_nat : Nf
| nf_pi : Nf -> Nf -> Nf
| nf_typ : nat -> Nf
| nf_zero : Nf
| nf_succ : Nf -> Nf
| nf_lam : Nf -> Nf.
(* Some convenient infix notations *)
Infix "∙" := a_compose (at level 70).
Infix ",," := a_extend (at level 80).


Notation Ctx := (list exp).
Notation Sb := subst.
Notation Typ := exp.
Notation typ := a_typ.
Notation ℕ := a_nat.
Notation 𝝺 := a_fn.
Notation Π := a_pi.


Fixpoint NeToExp (ne : Ne) : exp :=
  match ne with
  | ne_var n => a_var n
  | ne_rec T z s u => a_rec (NfToExp T) (NfToExp z) (NfToExp s) (NeToExp u) 
  | ne_app u n=> a_app (NeToExp u) (NfToExp n)
  end
with NfToExp (nf : Nf) : exp :=
  match nf with
  | nf_ne u => NeToExp u
  | nf_zero => a_zero
  | nf_succ w => a_succ (NfToExp w)
                   (* !!Wrong!! *)    
  | nf_lam w => a_fn (NfToExp w)(NfToExp w)
  | nf_nat => a_nat
  | nf_typ n => typ n
  | nf_pi M T => a_pi (NfToExp M) (NfToExp T)
  end.

