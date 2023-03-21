Require Import List.
Import ListNotations.

Require Import Mcltt.Syntax.

Reserved Notation "G |-" (at level 80).
Reserved Notation "G |- T" (no associativity, at level 80, T at next level).
Reserved Notation "G |- t : T" (no associativity, at level 80, t at next level).

Inductive wf_ctx : Ctx -> Set :=
  | empty : [] |-
  | ext : forall G a,
      G |- -> (a :: G) |-
where "G |- " := (wf_ctx G)
with wf_type : Ctx -> Typ -> Set :=
  | univ_e : forall G t i,
      G |- t : (typ i) -> G |- t
where "G |- t" := (wf_type G t)
with wf_term : Ctx -> exp -> Typ -> Set :=
  | univ_unit_f : forall G i,
      G |- -> G |- nat : (typ i)
where "G |- t : T" := (wf_term G t T).
