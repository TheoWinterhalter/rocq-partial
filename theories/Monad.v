(* (Yet another) description of monads *)

From Equations Require Import Equations.
From Stdlib Require Import Utf8 List Arith Lia.
Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Class Monad (M : Type → Type) := {
  ret : ∀ A, A → M A ;
  bind : ∀ A B, M A → (A → M B) → M B
}.

#[global] Hint Mode Monad ! : typeclass_instances.
Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Definition map {M} `{Monad M} {A B} (f : A → B) (m : M A) : M B :=
  bind m (λ x, ret (f x)).

Class MonadLift (M N : Type → Type) :=
  mlift : ∀ A, M A → N A.

Arguments mlift {M N _ A}.

#[export] Hint Mode MonadLift - ! : typeclass_instances.

Class MonadLiftT (M N : Type → Type) :=
  liftT : ∀ A, M A → N A.

Arguments liftT {M N _ A}.

#[export] Instance LiftT_refl M : MonadLiftT M M | 10 := λ A m, m.

#[export] Instance LiftT_step M N P `{MonadLift N P} `{MonadLiftT M N} :
  MonadLiftT M P | 5
:= λ A m, mlift (liftT m).

Module MonadNotations.

  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Open Scope monad_scope.

  Notation "c >>= f" :=
    (bind c f)
    (at level 50, left associativity) : monad_scope.

  Notation "x ← e ;; f" :=
    (bind e (λ x, f))
    (at level 100, e at next level, right associativity, format "x  ←  e ;;  f")
    : monad_scope.

  Notation "x ← e ;;[ M ] f" :=
    (bind (M:=M) e (λ x, f)) (
      at level 100,
      e at next level,
      M at level 50,
      right associativity,
      only parsing
    )
    : monad_scope.

  Notation "' pat ← e ;; f" :=
    (bind e (λ pat, f)) (
      at level 100,
      e at next level,
      right associativity,
      pat pattern,
      format "' pat  ←  e  ;;  f"
    )
    : monad_scope.

  Notation "' pat ← e ;;[ M ] f" :=
    (bind (M:=M) e (λ pat, f)) (
      at level 100,
      e at next level,
      M at level 50,
      right associativity,
      pat pattern,
      only parsing
    )
    : monad_scope.

  Notation "e ;; f" :=
    (bind e (λ _, f))
    (at level 100, right associativity)
    : monad_scope.

  Notation "e ;;[ M ] f" :=
    (bind (M:=M) e (λ _, f))
    (at level 100, M at level 50, right associativity, only parsing)
    : monad_scope.

  Notation "f '<*>' m" :=
    (map f m)
    (at level 50, left associativity)
    : monad_scope.

End MonadNotations.
