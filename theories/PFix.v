From Stdlib Require Import Utf8 RelationClasses.
From Partial Require Import Util Partial.
From Equations Require Import Equations.

Set Default Goal Selector "!".
(* Set Universe Polymorphism. *)
(* Set Polymorphic Inductive Cumulativity. *)
Set Primitive Projections.
Set Equations Transparent.
Unset Equations With Funext.

(** General recursion by recording call tree *)

Inductive orec A B C :=
| o_ret (x : C)
| o_grd (P : hProp) (κ : P → orec A B C)
| o_rec (x : A) (κ : B x → orec A B C).

Arguments o_ret {A B C}.
Arguments o_grd {A B C}.
Arguments o_rec {A B C}.

Section Graph.

  Context {A B} (f : ∀ (x : A), orec A B (B x)).

  Inductive orec_graph {a} : orec A B (B a) → B a → Prop :=
  | ret_graph x :
      orec_graph (o_ret x) x

  | grd_graph (P : hProp) κ v (h : P) :
      orec_graph (κ h) v →
      orec_graph (o_grd P κ) v

  | rec_graph x κ v w :
      orec_graph (f x) v →
      orec_graph (κ v) w →
      orec_graph (o_rec x κ) w.

  Definition graph x v :=
    orec_graph (f x) v.

  Inductive orec_lt {a} : A → orec A B (B a) → Prop :=
  | guard_lt P κ h x :
      orec_lt x (κ h) →
      orec_lt x (o_grd P κ)

  | top_lt x κ :
      orec_lt x (o_rec x κ)

  | rec_lt x κ v y :
        graph x v →
        orec_lt y (κ v) →
        orec_lt y (o_rec x κ).

  Derive Signature for orec_graph orec_lt.
  Derive NoConfusion NoConfusionHom for orec.

  Definition partial_lt x y :=
    orec_lt x (f y).

  Definition domain x :=
    ∃ v, graph x v.

  Lemma orec_graph_functional :
    ∀ a o v w,
      orec_graph (a := a) o v →
      orec_graph o w →
      v = w.
  Proof.
    intros a o v w hv hw.
    induction hv in w, hw |- *.
    - depelim hw. reflexivity.
    - depelim hw. cbn in hw.
      assert (h = h0) as <-.
      { apply isprop. }
      firstorder.
    - depelim hw.
      assert (v = v0) as <-.
      { firstorder. }
      firstorder.
  Qed.

  Lemma graph_functional x v w :
    graph x v →
    graph x w →
    v = w.
  Proof.
    intros hv hw.
    eapply orec_graph_functional. all: eassumption.
  Qed.

  Lemma partial_lt_acc :
    ∀ x,
      domain x →
      Acc partial_lt x.
  Proof.
    intros x h.
    destruct h as [v h].
    constructor. intros x' h'.
    red in h. red in h'.
    set (o := f _) in *. clearbody o.
    induction h in x', h' |- *.
    - depelim h'.
    - depelim h'. cbn in h'.
      assert (h = h1) as <-.
      { apply isprop. }
      firstorder.
    - depelim h'.
      + constructor. intros y h.
        apply IHh1. assumption.
      + assert (v = v0).
        { eapply orec_graph_functional. all: eassumption. }
        subst.
        apply IHh2. assumption.
  Qed.

  Lemma lt_preserves_domain :
    ∀ x y,
      domain x →
      partial_lt y x →
      domain y.
  Proof.
    intros x y h hlt.
    destruct h as [v h].
    red in hlt. red in h.
    set (o := f _) in *. clearbody o.
    induction h in y, hlt |- *.
    - depelim hlt.
    - depelim hlt. cbn in hlt.
      assert (h = h1) as <-.
      { apply isprop. }
      firstorder.
    - depelim hlt.
      + eexists. eassumption.
      + assert (v = v0).
        { eapply orec_graph_functional. all: eassumption. }
        subst.
        apply IHh2. assumption.
  Qed.

  Abbreviation sigmaarg :=
    (sigma (λ x, domain x)).

  #[local] Instance wf_partial :
    WellFounded (λ (x y : sigmaarg), partial_lt (pr1 x) (pr1 y)).
  Proof.
    (* eapply Acc_intro_generator with (1 := acc_fuel). *)
    intros [x h].
    pose proof (partial_lt_acc x h) as hacc.
    induction hacc as [x hacc ih] in h |- *.
    constructor. intros [y h'] hlt.
    apply ih. assumption.
  Defined.

  (* We need this for the proofs to go through *)
  Opaque wf_partial.

  Definition image x :=
    { v | graph x v }.

  Definition oimage {a} (o : orec A B (B a)) :=
    { v | orec_graph o v }.

  Definition orec_domain {a} (o : orec A B (B a)) :=
    ∃ v, orec_graph o v.

  (* The calls to depelim in orec_inst create a lot of universes
     That's probably a bug/shortcoming of equation but for now
     we derive explicitly the two inversion principles that are required.
   *)
  Lemma orec_graph_rec_inv {a x κ} {w : B a} (e : orec_graph (o_rec x κ) w) :
    ∃ v, orec_graph (f x) v ∧ orec_graph (κ v) w.
  Proof.
    refine (match e in orec_graph m r return
                  match m with
                  | o_rec x κ => ∃ v, orec_graph (f x) v ∧ orec_graph (κ v) r
                  | _ => True
                  end
            with
            | rec_graph _ _ _ _ _ _ => _
            | _ => _
            end); try constructor.
    eexists; split; eassumption.
  Qed.

  (* orec_inst should no introduce any universe, but we cannot specify it because of Equations *)
  Equations? orec_inst@{+} {a} (e : orec A B (B a)) (de : orec_domain e)
    (da : domain a)
    (ha : ∀ x, orec_lt x e → partial_lt x a)
    (r : ∀ y, domain y → partial_lt y a → oimage (f y)) : oimage e :=
    orec_inst (o_ret v) de da ha r := ⟨ v ⟩ ;
    orec_inst (o_grd P κ) de da ha r := ⟨ ((orec_inst (κ _) _ _ _ r)) ∙1 ⟩ ;
    orec_inst (o_rec x κ) de da ha r := ⟨ ((orec_inst (κ ((r x _ _) ∙1)) _ _ _ r)) ∙1 ⟩.
  Proof.
    - constructor.
    - red in de. destruct de as [v de]. depelim de. assumption.
    - red in de. destruct de as [v de]. depelim de. cbn. firstorder.
    - apply ha. econstructor. eassumption.
    - red in de. destruct de as [v de]. depelim de. cbn.
      destruct orec_inst. simpl.
      econstructor.
      assert (v = x).
      { eapply orec_graph_functional.
        all: eauto.
      }
      subst. eauto.
    - eapply lt_preserves_domain. 1: eassumption.
      apply ha. constructor.
    - apply ha. constructor.
    - destruct de as [v hg].
      pose proof (orec_graph_rec_inv hg) as (v0&?&?).
      simpl in *.
      destruct r as [w hw]. simpl.
      assert (w = v0).
      { eapply orec_graph_functional.
        all: eassumption.
      }
      subst.
      eexists. eassumption.
    - apply ha. econstructor. 2: eassumption.
      red. destruct r. assumption.
    - simpl. destruct orec_inst. simpl.
      econstructor. 2: eassumption.
      destruct r. assumption.
  Defined.

  #[derive(equations=no),tactic=idtac]
  Equations? def_p (x : A) (h : domain x) : oimage (f x)
    by wf x partial_lt :=
    def_p x h := orec_inst (a := x) (f x) h h (λ x Hx, Hx) (λ y hy hr, def_p y hy).
  Proof.
    exact hr.
  Defined.

  Definition def x h :=
    (def_p x h) ∙1.

  Lemma def_graph_sound :
    ∀ x h,
      graph x (def x h).
  Proof.
    intros x h.
    unfold def. destruct def_p. assumption.
  Qed.

  Lemma domain_prop x :
    ∀ (h1 h2 : domain x), h1 = h2.
  Proof.
    (* Would follow from PI, probably doable without *)
  Admitted.

End Graph.

#[refine]
Definition pfix {A B} (f : ∀ (x : A), orec A B (B x)) (a : A) : partial (B a) :=
  guarded (mkprop (domain f a) _) (def _ _).
Proof.
  apply domain_prop.
Defined.

Lemma pfix_graph A B f a h :
  graph f a (value (@pfix A B f a) h).
Proof.
  cbn in *. apply def_graph_sound.
Qed.

Lemma graph_pfix A B f a v :
  graph f a v →
  @pfix A B f a ↦ v.
Proof.
  intros h.
  split.
  - cbn. exists v. assumption.
  - cbn. intros p.
    pose proof (def_graph_sound _ _ p) as h'.
    eapply graph_functional. all: eassumption.
Qed.

Fixpoint orec_apply {A B C} (e : orec A B C) f :=
  match e with
  | o_ret v => ret v
  | o_grd P k => bind (guard P) (λ h, orec_apply (k h) f)
  | o_rec a k => bind (f a) (λ x, orec_apply (k x) f)
  end.

Lemma orec_graph_apply A B (f : ∀ x, orec A B (B x)) a o (v : B a) :
  orec_graph f o v →
  orec_apply o (pfix f) ↦ v.
Proof.
  induction 1 as [a x | a P k v h hk ih | a a' k b' b hf ihf hk ihk].
  - cbn. apply hasdef_ret.
  - cbn. eapply hasdef_bind. 2: eassumption.
    apply hasdef_guard.
  - cbn. eapply hasdef_bind.
    + apply graph_pfix. eassumption.
    + assumption.
Qed.

Lemma pfix_unfold A B f a :
  @pfix A B f a ≲ orec_apply (f a) (pfix f).
Proof.
  split.
  - intros [v h]. unfold graph in h.
    eapply orec_graph_apply in h.
    apply h.
  - cbn. intros [v h] q.
    unfold graph in h. apply orec_graph_apply in h as e.
    destruct e as [p e]. rewrite e.
    eapply graph_functional. 2: eassumption.
    apply def_graph_sound.
Qed.

(** orec is a monad *)

Fixpoint orec_bind {A B C D} (o : orec A B C) (d : C → orec A B D) :=
  match o with
  | o_ret c => d c
  | o_grd P k => o_grd P (λ h, orec_bind (k h) d)
  | o_rec x k => o_rec x (λ v, orec_bind (k v) d)
  end.

(** Partial functions compose through orec *)

Definition lift {A B C} (u : partial C) : orec A B C :=
  o_grd (defined u) (λ h, o_ret (value u h)).
