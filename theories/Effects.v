From Equations Require Import Equations.
From Stdlib Require Import Utf8 String List Arith Lia.
From Partial Require Import Util Monad Partial PFix.
Import MonadNotations.

Class MonadCall (A : Type) (C : A → Type) (M : Type → Type) :=
  call : ∀ x, M (C x).

Arguments call {A C M _} x.

#[export] Hint Mode MonadCall - - ! : typeclass_instances.

#[export] Instance Call_orec {A B} : MonadCall A B (orec A B) :=
  λ x, o_rec x o_ret.

Inductive exn E A :=
| success (x : A)
| exception (e : E).

Arguments success {E A}.
Arguments exception {E A}.

Definition ExnT E (M : Type → Type) (A : Type) : Type := M (exn E A).

#[export] Instance Monad_ExnT E M `{Monad M} : Monad (ExnT E M) := {|
  ret A x := ret (M := M) (success x) ;
  bind A B c f :=
    bind (M := M) c (λ r,
      match r with
      | success y => f y
      | exception e => ret (M := M) (exception e)
      end
    )
|}.

Class MonadRaise E (M : Type → Type) :=
  raise : ∀ A, E → M A.

Arguments raise {E M _ A} e.

#[export] Hint Mode MonadRaise - ! : typeclass_instances.

#[export] Instance Raise_ExnT E M `{Monad M} : MonadRaise E (ExnT E M) :=
  λ A e, ret (M := M) (exception e).

#[export] Instance Lift_ExnT E M `{Monad M} : MonadLift M (ExnT E M) :=
  λ A m, bind (M := M) m (λ a, ret (M := M) (success a)).

#[export] Instance LiftCong_ExnT E M N `{MonadLift M N} :
  MonadLift (ExnT E M) (ExnT E N) :=
  λ A m, one_step_lift (A := exn E A) m.

Definition catch {E M} `{Monad M} {A} (m : ExnT E M A) (h : E → ExnT E M A) :
  ExnT E M A :=
  bind (M := M) m (λ r,
    match r with
    | success y => ret (M := M) (success y)
    | exception e => h e
    end
  ).

#[export] Instance Call_ExnT {E A C} :
  MonadCall A C (ExnT E (orec A (λ x, exn E (C x)))) :=
  λ x, o_rec x o_ret.

Definition pfixExn {E A} {C : A → Type}
  (f : ∀ x, ExnT E (orec A (λ x, exn E (C x))) (C x)) :
  ∀ x, ExnT E partial (C x) :=
  λ x, pfix (B := λ x, exn E (C x)) f x.
