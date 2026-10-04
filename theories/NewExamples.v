From Equations Require Import Equations.
From Stdlib Require Import Utf8 List Arith Lia.
From Partial Require Import Util Monad Partial PFix.
Import MonadNotations.

Definition collatz : nat → partial nat :=
  pfix (λ n,
    if n =? 1 then ret 0
    else o_rec (if Nat.even n then n / 2 else 3 * n + 1) (λ x, o_ret (S x))
  ).

Definition test : nat → partial nat :=
  pfix (λ n,
    if n =? 0 then ret 0
    else
      k ← liftT (collatz n) ;;
      o_rec (n - 1) (λ r, o_ret (k + r))
  ).
