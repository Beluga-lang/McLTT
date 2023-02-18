Require Export String.
Require Export List.


Inductive cst_term : Type :=
 | cType (level : nat)
 | cNat
 | cVar (s : string)
 | cZero
 | cSucc (t : cst_term)
 | cFun (s : string) (t : cst_term)
 | cApp (t1 : cst_term) (t2 : cst_term).

Inductive ast_term : Type :=
 | aType (level : nat)
 | aNat
 | aVar (n : nat)
 | aZero
 | aSucc (t : ast_term)
 | aFun (t : ast_term)
 | aApp (t1 : ast_term) (t2 : ast_term).


(**De-monadify with pattern matching for now**)
Fixpoint lookup (s : string) (ctx : list string) (index : nat) : (option nat) :=
 match ctx with
  | nil => None
  | c::cs => if eqb c s then (Some index) else lookup s cs (index+1) 
 end
.



Definition ret {A : Type} (x : A) := Some x.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Search (  option ?A -> (?A-> option ?B) -> option ?B).

Definition compose {A B C : Type} (f : A -> B) (g : B -> C) : A -> C := fun x => g (f x).


Fixpoint elaborate (cst : cst_term) (ctx : list string) : (option ast_term) :=
 match cst with 
 | cType n => Some (aType n)
 | cNat => Some aNat
 | cZero => Some aZero
 | cSucc c => (elaborate c ctx) >>= (compose aSucc ret)
 | cVar s =>  (lookup s ctx 0) >>= (compose aVar ret)
 | cFun s c => (elaborate c (s::ctx)) >>= (compose aFun ret)
 | cApp c1 c2 => (elaborate c1 ctx) >>= (fun c1 => (elaborate c2 ctx) >>= (compose (aApp c1) ret))
 end
.

Check elaborate cNat nil : option ast_term.
Fail Check elaborate (cSucc aNat) : option ast_term.

Compute (elaborate (cFun "s" (cVar "s")) nil).
Compute (elaborate (cFun "s" (cFun "x" (cApp (cVar "x") (cVar "s")))) nil).
Compute (elaborate (cFun "s" (cFun "x" (cFun "s" (cVar "s")))) nil).
Compute (elaborate (cFun "s" (cFun "x" (cFun "s" (cVar "q")))) nil).


Example test_elab : elaborate cNat nil = Some aNat.
Proof. reflexivity. Qed.

Example test_elab2 : elaborate (cFun "s" (cFun "x" (cFun "s" (cVar "q")))) nil = None.
Proof. reflexivity. Qed.




