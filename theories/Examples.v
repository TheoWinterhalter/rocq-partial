From Equations Require Import Equations.
From Stdlib Require Import
  Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Stdlib Require Import Utf8 String List Arith Lia.
From Partial Require Import Util Monad Partial PFix Effects.
Import MonadNotations.

Extraction Language OCaml.

Definition collatz : nat → partial nat :=
  pfixRec (λ collatz n,
    if n =? 1 then ret 0
    else
      x ← collatz (if Nat.even n then n / 2 else 3 * n + 1) ;;
      ret (S x)
  ).

Definition test : nat → partial nat :=
  pfixRec (λ test n,
    if n =? 0 then ret 0
    else
      k ← lift (collatz n) ;;
      r ← test (n - 1) ;;
      ret (k + r)
  ).

(** Combining with effects, first exceptions *)

(** Number of Collatz steps; raises on 0 (which would loop forever). *)
Definition collatz_steps : nat → ExnT string partial nat :=
  pfixExn (λ collatz_steps n,
    if n =? 0 then raise "collatz: zero"%string
    else if n =? 1 then ret 0
    else
      r ← collatz_steps (if Nat.even n then n / 2 else 3 * n + 1) ;;
      ret (S r)
  ).

(**
  Sums [collatz_steps] over [n, n-1, ..., 0]. The exception raised at 0
  propagates through the recursion without any explicit matching.
*)
Definition total_steps : nat → ExnT string partial nat :=
  pfixExn (λ total_steps n,
    k ← lift (collatz_steps n) ;;
    if n =? 0 then ret k
    else
      r ← total_steps (n - 1) ;;
      ret (k + r)
  ).

(** Same, but recovers from the error with [catch]. *)
Definition total_steps_safe : nat → ExnT string partial nat :=
  pfixExn (λ total_steps_safe n,
    k ← catch (lift (collatz_steps n)) (λ _, ret 0) ;;
    if n =? 0 then ret k
    else
      r ← total_steps_safe (n - 1) ;;
      ret (k + r)
  ).

(** Now state *)

(** Collatz, logging every visited value in the state. Returns the number of steps. *)
Definition collatz_trace : nat → list nat → partial (nat * list nat) :=
  pfixState (λ collatz_trace n,
    modify (cons n) ;;
    if n =? 1 then ret 0
    else
      r ← collatz_trace (if Nat.even n then n / 2 else 3 * n + 1) ;;
      ret (S r)
  ).

(** Max value reached, with a step counter as state. *)
Definition collatz_max : nat → nat → partial (nat * nat) :=
  pfixState (λ collatz_max n,
    modify S ;;
    if n =? 1 then ret 1
    else
      m ← collatz_max (if Nat.even n then n / 2 else 3 * n + 1) ;;
      ret (Nat.max n m)
  ).

(** A partial function typeofed from a stateful one through [liftT]. *)
Definition collatz_len : nat → partial nat :=
  pfixRec (λ collatz_len n,
    if n =? 1 then ret 0
    else
      r ← collatz_len (if Nat.even n then n / 2 else 3 * n + 1) ;;
      ret (S r)
  ).

Definition sum_lens : nat → nat → partial (nat * nat) :=
  pfixState (λ sum_lens n,
    k ← lift (collatz_len n) ;;
    modify (Nat.add k) ;;
    if n =? 1 then ret 0
    else
      r ← sum_lens (n - 1) ;;
      ret (k + r)
  ).

(** A tiny simply-typed lambda calculus. *)

Inductive ty : Type :=
| TNat
| TBool
| TArr : ty → ty → ty.

Inductive tm : Type :=
| TVar   : nat → tm
| TNatLit : nat → tm
| TTrue  : tm
| TFalse : tm
| TApp   : tm → tm → tm
| TLam   : ty → tm → tm
| TIf    : tm → tm → tm → tm.

(** Contexts use de Bruijn indices: variable 0 is the newest binding. *)

Fixpoint lookup_ty (n : nat) (Γ : list ty) : option ty :=
  match n, Γ with
  | 0, A :: _     => Some A
  | S n', _ :: Γ' => lookup_ty n' Γ'
  | _, _           => None
  end.

Definition ty_eqb : ty * ty → ExnT string partial bool :=
  pfixExn (λ ty_eqb '(A, B),
    match A, B with
    | TNat, TNat => ret true
    | TBool, TBool => ret true
    | TArr A1 A2, TArr B1 B2 =>
      b1 ← ty_eqb (A1, B1) ;;
      b2 ← ty_eqb (A2, B2) ;;
      ret (b1 && b2)%bool
    | _, _ => ret false
    end
  ).

(** Type checking. *)
Definition typeof : (list ty * tm) → ExnT string partial ty :=
  pfixExn (λ typeof '(Γ, t),
    match t with

    | TVar x =>
        match lookup_ty x Γ with
        | Some A => ret A
        | None   => raise "unbound variable"%string
        end

    | TNatLit _ =>
        ret TNat

    | TTrue =>
        ret TBool

    | TFalse =>
        ret TBool

    | TApp f a =>
        Tf ← typeof (Γ, f) ;;
        Ta ← typeof (Γ, a) ;;
        match Tf with
        | TArr A B =>
            b ← lift (ty_eqb (A, Ta)) ;;
            if b then
              ret B
            else
              raise "argument type mismatch"%string
        | _ =>
            raise "application of a non-function"%string
        end

    | TLam A body =>
        B ← typeof (A :: Γ, body) ;;
        ret (TArr A B)

    | TIf c t e =>
        Tc ← typeof (Γ, c) ;;
        match Tc with
        | TBool =>
            Tt ← typeof (Γ, t) ;;
            Te ← typeof (Γ, e) ;;
            b ← lift (ty_eqb (Tt, Te)) ;;
            if b then
              ret (Tt : ty)
            else
              raise "branches have different types"%string
        | _ =>
            raise "condition is not a boolean"%string
        end

    end
  ).

(** Some examples. *)

Definition id_nat : tm :=
  TLam TNat (TVar 0).

Definition good_app : tm :=
  TApp id_nat (TNatLit 42).

Definition bad_app : tm :=
  TApp id_nat TTrue.

Definition good_if : tm :=
  TIf TTrue (TNatLit 0) (TNatLit 1).

Definition bad_if : tm :=
  TIf TTrue (TNatLit 0) TFalse.

Definition typeof_x
  (Γ : list ty) (t : tm) : _ → exn string ty :=
  value (typeof (Γ, t)).

(** More examples to be put in their own files later *)

(** Calls read like ordinary applications of the function being defined. *)
Definition gcd : nat → nat → partial nat :=
  pfixRec2 (λ gcd a b,
    if b =? 0 then ret a else gcd b (a mod b)
  ).

(** Nested recursive calls, via the monad. *)
Definition ack : nat → nat → partial nat :=
  pfixRec2 (λ ack m n,
    match m, n with
    | 0, _ => ret (S n)
    | S m', 0 => ack m' 1
    | S m', S n' => k ← ack m n' ;; ack m' k
    end
  ).

(** Three arguments. *)
Definition sum_range : nat → nat → nat → partial nat :=
  pfixRec3 (λ sum lo hi acc,
    if hi <? lo then ret acc else sum (S lo) hi (acc + lo)
  ).

(** Exceptions. *)
Definition div_exact : nat → nat → ExnT string partial nat :=
  pfixExn2 (λ self a b,
    if b =? 0 then raise "division by zero"%string
    else if a =? 0 then ret 0
    else if a <? b then raise "not divisible"%string
    else r ← self (a - b) b ;; ret (S r)).

(** State: counts the calls. *)
Definition gcd_calls : nat → nat → nat → partial (nat * nat) :=
  pfixState2 (λ self a b,
    modify S ;;
    if b =? 0 then ret a else self b (a mod b)).

(** A body made only of calls never fixes its own result type: this is what
    the [&] hints are for. *)
Definition countdown : nat → nat → partial nat :=
  pfixRec2 (λ self a b, if a =? 0 then self 0 b else self (a - 1) b).

(* Unfolded wrappers for extraction *)
Definition gcd_x a b : _ → nat := value (gcd a b).
Definition ack_x a b : _ → nat := value (ack a b).
Definition sum_range_x a b c : _ → nat := value (sum_range a b c).
Definition div_exact_x a b : _ → exn string nat := value (div_exact a b).
Definition gcd_calls_x a b s : _ → nat * nat := value (gcd_calls a b s).

(** Extraction *)

(* Unfolding for extraction *)
Definition collatz_x n : _ → nat := value (collatz n).
Definition test_x n : _ → nat := value (test n).
Definition collatz_steps_x n : _ → exn string nat := value (collatz_steps n).
Definition total_steps_x n : _ → exn string nat := value (total_steps n).
Definition total_steps_safe_x n : _ → exn string nat :=
  value (total_steps_safe n).
Definition collatz_max_x n m : _ → nat * nat := value (collatz_max n m).
Definition collatz_trace_x n l : _ → nat * list nat :=
  value (collatz_trace n l).
Definition collatz_len_x n : _ → nat := value (collatz_len n).
Definition sum_lens_x n m : _ → nat * nat := value (sum_lens n m).

Extraction "extracted.ml" value
  collatz_x test
  collatz_steps_x total_steps_x total_steps_safe_x
  collatz_trace_x collatz_max_x collatz_len_x sum_lens_x
  id_nat good_app bad_app good_if bad_if typeof_x.
