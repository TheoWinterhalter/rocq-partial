From Equations Require Import Equations.
From Stdlib Require Import
  Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From Stdlib Require Import Utf8 String List Arith Lia.
From Partial Require Import Util Monad Partial PFix Effects.
Import MonadNotations.
Import ListNotations.

Extraction Language OCaml.

(** * Gallery of examples

  We showcase a few examples here, using effects beyond partiality or not.

*)

(** ** Basic usage

  Partiality allow you to leave certain cases undefined.
  This can be used in conjunction with the usual Rocq language constructs.

*)

Fixpoint minus (n m : nat) : partial nat :=
  match n, m with
  | 0, 0 => ret 0
  | _, 0 => ret n
  | S n, S m => minus n m
  | _,_ => undefined
  end.

(**

  It can also be used to restrict manually a domain.
  But this requires proving the restriction is a mere proposition
  (which can be proven using proof irrelevance if one doesn't mind).

*)

Definition nonzero n :=
  match n with
  | 0 => hFalse
  | _ => hTrue
  end.

Definition pred (n : nat) : partial nat :=
  h ← guard (nonzero n) ;;
  match n return nonzero n → _ with
  | S k => λ _, ret k
  | 0 => λ (h : False), match h with end
  end h.

(** In practice, using guard manually is often not needed: *)

Definition pred' n : partial nat :=
  match n with
  | S k => ret k
  | 0 => undefined
  end.

(** We can show [pred] and [pred'] are equivalent. *)

Lemma pred_equiv n :
  pred n ≈ pred' n.
Proof.
  split.
  - cbn. split.
    + intros [p h].
      destruct n. 1: contradiction.
      cbn. constructor.
    + intros h.
      destruct n. 1: contradiction.
      exists I. cbn. constructor.
  - intros p q. destruct n. 1: contradiction.
    reflexivity.
Qed.

(** We can also prove some other things *)

Lemma pred_S n :
  pred (S n) ↦ n.
Proof.
  split.
  - cbn. exists I. constructor.
  - cbn. reflexivity.
Qed.

(** Partial definitions can be composed with one another (it's a monad). *)

Definition pred_twice n :=
  k ← pred n ;;
  pred k.

(**

  More interestingly, we have access to general recursion.
  Below we look at the naive implementation of Euclid's algorithm, which swaps
  the arguments if they are not ordered properly.
  Such a function is typically painful to make Rocq acccept, even though it is
  total.

*)

Definition gcd : nat → nat → partial nat :=
  #pfix gcd a b,
    if a <? b then gcd b a
    else if b =? 0 then ret a
    else gcd (a - b) b.

(** We can show it is total after the fact. For instance with a measure. *)

Lemma gcd_def a b :
  defined (gcd a b).
Proof.
  apply compute_domain. cbn - ["<?"].
  pose (mes := a + 2 * b).
  lazymatch goal with
  | |- ?g => assert (h : ∀ n, mes < n → g)
  end.
  { intros n hmes. induction n as [| n ih] in a, b, mes, hmes |- *. 1: lia.
    destruct (a <? b) eqn: e.
    - cbn - ["<?"]. split. 2: auto.
      apply compute_domain. apply ih.
      rewrite Nat.ltb_lt in e. lia.
    - destruct (b =? 0) eqn: eb.
      + cbn. constructor.
      + cbn - ["<?"]. split. 2: auto.
        apply compute_domain. apply ih.
        rewrite Nat.ltb_ge in e.
        rewrite Nat.eqb_neq in eb.
        lia.
  }
  eapply h. econstructor.
Qed.

(** We can also use general recursion with dependently typed results *)

Inductive even : nat → Prop :=
| even0 : even 0
| evenS n : even n → even (S (S n)).

Arguments evenS {n}.

Definition toeven : ∀ n, partial (even n) :=
  #pfix aux n,
    match n with
    | 0 => ret even0
    | 1 => lift undefined
    | S (S n) => evenS <*> aux n
    end.

(** Note: we used [lift] to use [undefined] in the recursion monad. *)

Inductive fin : nat → Type :=
| f0 {n} : fin (S n)
| fS {n} : fin n → fin (S n).

Definition as_fin : ∀ {m}, nat → partial (fin m) :=
  #pfix af (m : nat) (n : nat),
    match m, n with
    | 0, _ => lift undefined
    | S m, 0 => ret f0
    | S m, S n => fS <*> af m n
    end.

(** We can use [lift] for any partial computation *)

Definition gcd_list n : list nat → partial (list nat) :=
  #pfix foo (l : list nat),
    match l with
    | [] => ret []
    | a :: l =>
      b ← lift (gcd n a) ;;
      l ← foo l ;;
      ret (b :: l)
    end.

(** ** Effects

  We can also use effects to, for instance, return exceptions instead of simply
  being undefined.

*)

Definition predX n : ExnT string partial nat :=
  match n with
  | S k => ret k
  | 0 => raise "pred of 0"%string
  end.

(** For #pfix, you need to specify the combinator. *)

Definition as_finX : ∀ {m}, nat → ExnT string partial (fin m) :=
  #pfix[ pfixExnU ] af (m : nat) (n : nat),
    match m, n with
    | 0, _ => raise "Too big to fit."%string
    | S m, 0 => ret f0
    | S m, S n => fS <*> af m n
    end.

(** Simply typed λ-calculus inference *)

Inductive ty :=
| Bool
| Arr (A B : ty).

Inductive tm :=
| var (n : nat)
| tru
| fas
| ifte (b t f : tm)
| ap (u v : tm)
| lam (A : ty) (t : tm).

Definition ctx := list ty.

Definition eqty : ty → ty → ExnT string partial unit :=
  #pfix[ pfixExnU ] eqty A B,
    match A, B with
    | Bool, Bool => ret tt
    | Arr A1 A2, Arr B1 B2 =>
      eqty A1 B1 ;;
      eqty A2 B2
    | _, _ => raise "Arr ≠ Bool"%string
    end.

Definition infer : ctx → tm → ExnT string partial ty :=
  #pfix[ pfixExnU ] inf Γ t,
    match t with
    | var n =>
      match nth_error Γ n with
      | Some A => ret A
      | None => raise "Unbound variable"%string
      end
    | tru => ret Bool
    | fas => ret Bool
    | ifte b t f =>
      iB ← inf Γ b ;;
      (* eqty iB Bool ;; *)
      T ← inf Γ t ;;
      F ← inf Γ f ;;
      (* eqty T F ;; *)
      ret T
    | ap u v =>
      iAB ← inf Γ u ;;
      match iAB with
      | Arr A B =>
        iA ← inf Γ v ;;
        (* eqty iA A ;; *)
        ret B
      | _ => raise "Cannot be applied"%string
      end
    | lam A t =>
      B ← inf (A :: Γ) t ;;
      ret (Arr A B)
    end.

(** Some terms to test *)

Definition idbool :=
  lam Bool (var 0).

Definition ok :=
  ap idbool tru.

Definition ko :=
  ap idbool idbool.

Definition good_if :=
  ifte fas ok ok.

Definition bad_if :=
  ifte fas idbool ok.

(** Now state *)

(* This raises an anomaly *)
(* Definition list_sum : list nat → StateT nat partial nat :=
  put 0 ;;
  (#pfix[ pfixStateU ] aux l,
    match l with
    | [] => get
    | n :: l =>
      modify (max n) ;;
      aux l
    end) ;;
  get. *)

Definition sum_nums : nat → nat → partial (nat * nat) :=
  #pfix[ pfixStateU ] aux n,
    modify (Nat.add n) ;;
    if n =? 1 then ret 0
    else aux (n - 1).

(** Extraction *)

(* Unfolding for extraction *)
Definition minux_x n m := value (minus n m).
Definition pred_x n := value (pred n).
Definition pred'_x n := value (pred' n).
Definition pred_twice_x n := value (pred_twice n).
Definition gcd_x a b := value (gcd a b).
Definition toeven_x n := value (toeven n).
Definition as_fin_x m n := value (@as_fin m n).
Definition gcd_list_x n l := value (gcd_list n l).
Definition predX_x n := value (predX n).
Definition as_finX_x m n := value (@as_finX m n).
Definition eqty_x A B := value (eqty A B).
Definition infer_x Γ t := value (infer Γ t).

Extraction "extracted.ml" value
  minux_x pred_x pred'_x pred_twice_x gcd_x toeven_x as_fin_x predX_x as_finX_x
  gcd_list_x eqty_x infer_x idbool ok good_if bad_if.
