From Stdlib Require Import Utf8 RelationClasses.
From Equations Require Import Equations.

Set Default Goal Selector "!".
(* Set Universe Polymorphism. *)
(* Set Polymorphic Inductive Cumulativity. *)
Set Primitive Projections.
Set Equations Transparent.
Unset Equations With Funext.

Notation "t ∙1" := (proj1_sig t) (at level 1).
Notation "⟨ x ⟩" := (exist _ x _) (only parsing).
Notation "⟨ x | h ⟩" := (exist _ x h).

Lemma reflexive_eq A R `{Reflexive A R} x y :
  x = y →
  R x y.
Proof.
  intros []. reflexivity.
Qed.

Record hProp := mkprop {
  prop :> Prop ;
  isprop : ∀ (x y : prop), x = y
}.

#[refine]
Definition hTrue :=
  mkprop True _.
Proof.
  intros [] []. reflexivity.
Defined.

#[refine]
Definition hFalse :=
  mkprop False _.
Proof.
  intros [].
Defined.
