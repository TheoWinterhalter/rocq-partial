From Equations Require Import Equations.
From Stdlib Require Import
  Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Stdlib Require Import Utf8 String List Arith Lia.
From Partial Require Import Util Monad Partial PFix.
Import MonadNotations.

Extraction Language OCaml.

Definition collatz : nat → partial nat :=
  pfix (λ n,
    if n =? 1 then ret 0
    else o_rec (if Nat.even n then n / 2 else 3 * n + 1) (λ x, o_ret (S x))
  ).

Definition test : nat → partial nat :=
  pfix (λ n,
    if n =? 0 then ret 0
    else
      k ← lift (collatz n) ;;
      o_rec (n - 1) (λ r, o_ret (k + r))
  ).

(** Combining with effects, first exceptions *)

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

(** Number of Collatz steps; raises on 0 (which would loop forever). *)
Definition collatz_steps : nat → ExnT string partial nat :=
  pfixExn (λ n,
    if n =? 0 then raise "collatz: zero"%string
    else if n =? 1 then ret 0
    else
      r ← call (if Nat.even n then n / 2 else 3 * n + 1) ;;
      ret (S r)
  ).

(**
  Sums [collatz_steps] over [n, n-1, ..., 0]. The exception raised at 0
  propagates through the recursion without any explicit matching.
*)
Definition total_steps : nat → ExnT string partial nat :=
  pfixExn (λ n,
    k ← lift (collatz_steps n) ;;
    if n =? 0 then ret k
    else
      r ← call (n - 1) ;;
      ret (k + r)
  ).

(** Same, but recovers from the error with [catch]. *)
Definition total_steps_safe : nat → ExnT string partial nat :=
  pfixExn (λ n,
    k ← catch (lift (collatz_steps n)) (λ _, ret 0) ;;
    if n =? 0 then ret k
    else
      r ← call (n - 1) ;;
      ret (k + r)
  ).

(** Extraction *)

(* Unfolding for extraction *)
Definition collatz_x n : _ → nat := value (collatz n).
Definition test_x n : _ → nat := value (test n).
Definition collatz_steps_x n : _ → exn string nat := value (collatz_steps n).
Definition total_steps_x n : _ → exn string nat := value (total_steps n).
Definition total_steps_safe_x n : _ → exn string nat :=
  value (total_steps_safe n).

Extraction "extracted.ml" value
  collatz_x test
  collatz_steps_x total_steps_x total_steps_safe_x.
