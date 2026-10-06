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

(** Plain recursion

  Necessary to help unification somehow.

*)

Definition Rec A (B : A → Type) (C : Type) : Type := orec A B C.

#[export] Instance Monad_Rec {A B} : Monad (Rec A B) := Monad_orec.

#[export] Instance Call_Rec {A B} : MonadCall A B (Rec A B) :=
  λ x, o_rec x o_ret.

#[export] Instance Lift_partial_Rec {A B} : MonadLift partial (Rec A B) :=
  λ C u, lift u.

Definition pfixRec {A B} (F : (∀ a, Rec A B (B a)) → ∀ a, Rec A B (B a)) a :
  partial (B a)
:= pfix (F call) a.

Arguments pfixRec {A B} & F.

Definition pfixRec2 {A B C}
  (F :
    (∀ a b, Rec (A * B) (λ p, C (fst p) (snd p)) (C a b)) →
    (∀ a b, Rec (A * B) (λ p, C (fst p) (snd p)) (C a b))
  ) a b : partial (C a b)
:=
  Eval cbn zeta in
  let def :=
    pfixRec
      (A := A * B)
      (B := λ p, C (fst p) (snd p))
      (λ f p, F (λ a b, f (a,b)) (fst p) (snd p)) (a,b)
  in def.

Arguments pfixRec2 {A B C} & F.

Definition pfixRec3 {A B C D}
  (F :
    (∀ a b c, Rec (A * B * C) (λ '(a,b,c), D a b c) (D a b c)) →
    (∀ a b c, Rec (A * B * C) (λ '(a,b,c), D a b c) (D a b c))
  ) a b c : partial (D a b c)
:=
  Eval cbn zeta in
  let def :=
    pfixRec
      (A := A * B * C)
      (B := λ '(a,b,c), D a b c)
      (λ f '(a,b,c), F (λ a b c, f (a,b,c)) a b c) (a,b,c)
  in def.

Arguments pfixRec3 {A B C D} & F.

(** Exceptions *)

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

Definition pfixExn {E A B}
  (F :
    (∀ a, ExnT E (orec A (λ x, exn E (B x))) (B a)) →
    (∀ a, ExnT E (orec A (λ x, exn E (B x))) (B a))
  ) a : ExnT E partial (B a)
:=
  pfix (B := λ x, exn E (B x)) (F call) a.

Arguments pfixExn {E A B} & F.

Definition pfixExn2 {E A B C}
  (F :
    (∀ a b, ExnT E (orec (A * B) (λ p, exn E (C (fst p) (snd p)))) (C a b)) →
    (∀ a b, ExnT E (orec (A * B) (λ p, exn E (C (fst p) (snd p)))) (C a b))
  ) a b : ExnT E partial (C a b) :=
  Eval cbn zeta in
  let def :=
    pfixExn
      (A := A * B) (B := λ p, C (fst p) (snd p))
      (λ f p, F (λ a b, f (a,b)) (fst p) (snd p)) (a, b)
  in def.

Arguments pfixExn2 {E A B C} & F.

(** State *)

Class MonadState S (M : Type → Type) := {
  get : M S ;
  put : S → M unit
}.

Arguments get {S M _}.
Arguments put {S M _} s.

#[export] Hint Mode MonadState - ! : typeclass_instances.

Definition modify {S M} `{MonadState S M} `{Monad M} (f : S → S) : M unit :=
  s ← get ;;
  put (f s).

Definition StateT S (M : Type → Type) (A : Type) : Type :=
  S → M (A * S)%type.

#[export] Instance Monad_StateT S M `{Monad M} : Monad (StateT S M) := {|
  ret A a := λ s, ret (M := M) (a, s) ;
  bind A B m k := λ s, bind (M := M) (m s) (λ '(a, s'), k a s')
|}.

#[export, refine] Instance State_StateT S M `{Monad M} : MonadState S (StateT S M) := {|
  get := λ s, ret (M := M) (s, s) ;
  put := λ s' _, ret (M := M) (_, s')
|}.
Proof.
  exact tt. (* If I give it above it doesn't work?? *)
Defined.

#[export] Instance Lift_StateT S M `{Monad M} : MonadLift M (StateT S M) :=
  λ A m s, bind (M := M) m (λ a, ret (M := M) (a, s)).

#[export] Instance Raise_StateT E S M `{MonadRaise E M} : MonadRaise E (StateT S M) :=
  λ A e s, raise e.

(** Recursion with state: the state is threaded through the call as an
    extra argument and result. *)
#[export] Instance Call_StateT {S A C} :
  MonadCall A C (StateT S (orec (A * S) (λ p, C (fst p) * S)%type)) :=
  λ x s, o_rec (x, s) o_ret.

Definition pfixState {S A B}
  (F :
    (∀ a, StateT S (orec (A * S) (λ p, (B (fst p)) * S)%type) (B a)) →
    (∀ a, StateT S (orec (A * S) (λ p, (B (fst p)) * S)%type) (B a))
  ) a (s : S) : partial (B a * S)%type
:=
  pfix
    (A := (A * S)%type)
    (B := λ p, ((B (fst p)) * S)%type)
    (λ p, F call (fst p) (snd p)) (a, s).

Arguments pfixState {S A B} & F.

Definition pfixState2 {S A B C}
  (F :
    (∀ a b,
      StateT S (orec ((A * B) * S) (λ p, C (fst (fst p)) (snd (fst p)) * S)%type) (C a b)
    ) →
    (∀ a b,
      StateT S (orec ((A * B) * S) (λ p, C (fst (fst p)) (snd (fst p)) * S)%type) (C a b)
    )
  ) a b :
  StateT S partial (C a b) :=
  Eval cbn zeta in
  let def :=
    pfixState
      (B := λ p, C (fst p) (snd p))
      (λ self p, F (λ a b, self (a, b)) (fst p) (snd p))
      (a,b)
  in def.

Arguments pfixState2 {S A B C} & F.
