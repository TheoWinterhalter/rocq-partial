From Equations Require Import Equations.
From Stdlib Require Import
  Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Stdlib Require Import Utf8 String List Arith Lia.
From Partial Require Import Util Monad Partial PFix Effects.
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
