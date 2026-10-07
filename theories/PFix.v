From Stdlib Require Import Utf8 RelationClasses.
From Partial Require Import Util Monad Partial.
From Equations Require Import Equations.
Import MonadNotations.

Set Default Goal Selector "!".
(* Set Universe Polymorphism. *)
(* Set Polymorphic Inductive Cumulativity. *)
Set Primitive Projections.
Set Equations Transparent.
Unset Equations With Funext.

(** General recursion by recording call tree *)

Inductive orec A B C :=
| o_ret (x : C)
| o_grd (P : hProp) (k : P → orec A B C)
| o_rec (x : A) (k : B x → orec A B C).

Arguments o_ret {A B C}.
Arguments o_grd {A B C}.
Arguments o_rec {A B C}.

Section Fix.

  Context {A B} (f : ∀ (x : A), orec A B (B x)).

  Inductive orec_graph {a} : orec A B (B a) → B a → Prop :=
  | ret_graph x :
      orec_graph (o_ret x) x

  | grd_graph (P : hProp) k v (h : P) :
      orec_graph (k h) v →
      orec_graph (o_grd P k) v

  | rec_graph x k v w :
      orec_graph (f x) v →
      orec_graph (k v) w →
      orec_graph (o_rec x k) w.

  Definition graph x v :=
    orec_graph (f x) v.

  Inductive orec_lt {a} : A → orec A B (B a) → Prop :=
  | guard_lt P k h x :
      orec_lt x (k h) →
      orec_lt x (o_grd P k)

  | top_lt x k :
      orec_lt x (o_rec x k)

  | rec_lt x k v y :
        graph x v →
        orec_lt y (k v) →
        orec_lt y (o_rec x k).

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
  Lemma orec_graph_rec_inv {a x k} {w : B a} (e : orec_graph (o_rec x k) w) :
    ∃ v, orec_graph (f x) v ∧ orec_graph (k v) w.
  Proof.
    refine (match e in orec_graph m r return
                  match m with
                  | o_rec x k => ∃ v, orec_graph (f x) v ∧ orec_graph (k v) r
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
    orec_inst (o_grd P k) de da ha r := ⟨ ((orec_inst (k _) _ _ _ r)) ∙1 ⟩ ;
    orec_inst (o_rec x k) de da ha r := ⟨ ((orec_inst (k ((r x _ _) ∙1)) _ _ _ r)) ∙1 ⟩.
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

  Scheme orec_graph_ind_dep := Induction for orec_graph Sort Prop.

  Definition rec_pack {a} x (k : B x → orec A B (B a)) (s : oimage (f x))
  (t : oimage (k (proj1_sig s))) : oimage (o_rec x k) :=
    exist _ (proj1_sig t)
      (rec_graph x k (proj1_sig s) (proj1_sig t) (proj2_sig s) (proj2_sig t)).

  Lemma rec_pack_eq {a} x (k : B x → orec A B (B a)) (s s' : oimage (f x)) t t' :
    s = s' →
    (∀ t'' : oimage (k (proj1_sig s)), t = t'') →
    rec_pack x k s t = rec_pack x k s' t'.
  Proof. intros E H. destruct E. f_equal. apply H. Qed.

  Lemma oimage_prop_aux {a} (o : orec A B (B a)) v (d : orec_graph o v) :
    ∀ s' : oimage o, ⟨ v | d ⟩ = s'.
  Proof.
    induction d as [a x | a P k v h d ih | a x k v1 w e1 ih1 e2 ih2]
    using orec_graph_ind_dep.
    - intros [w d']. depelim d'. reflexivity.
    - intros [w d']. depelim d'.
      assert (h0 = h) as ->. { apply isprop. }
      exact (f_equal (λ s : oimage (k h),
              ⟨ proj1_sig s | grd_graph P k (proj1_sig s) h (proj2_sig s) ⟩)
            (ih ⟨ w | d' ⟩)).
    - intros [w' d']. depelim d'.
      match goal with
      | |- _ = ⟨ ?w' | rec_graph _ _ ?v1' _ ?e1' ?e2' ⟩ =>
          exact (rec_pack_eq x k ⟨ v1 | e1 ⟩ ⟨ v1' | e1' ⟩ ⟨ w | e2 ⟩ ⟨ w' | e2' ⟩
                  (ih1 _) ih2)
      end.
  Qed.

  Lemma oimage_prop a (o : orec A B (B a)) (s s' : oimage o) : s = s'.
  Proof. destruct s as [v d]. apply oimage_prop_aux. Qed.

  Lemma domain_prop x :
    ∀ (h1 h2 : domain x), h1 = h2.
  Proof.
    intros [v hv] [w hw].
    exact (f_equal (λ s : oimage (f x), ex_intro (graph x) (proj1_sig s) (proj2_sig s))
                 (oimage_prop x (f x) (exist _ v hv) (exist _ w hw))).
  Qed.

  (** Functional induction on fixed points *)

  Abbreviation precond := (A → Prop).
  Abbreviation postcond := (∀ x, B x → Prop).

  Fixpoint orec_ind_step a (pre : precond) (post : postcond) (o : orec A B _) :=
    match o with
    | o_ret v => post a v
    | o_grd P k => ∀ h, orec_ind_step a pre post (k h)
    | o_rec x k => pre x ∧ ∀ v, post x v → orec_ind_step a pre post (k v)
    end.

  Definition funind (pre : precond) post :=
    ∀ x, pre x → orec_ind_step x pre post (f x).

  Lemma orec_graph_inst_ind_step pre post x o v :
    funind pre post →
    orec_ind_step x pre post o →
    pre x →
    orec_graph o v →
    post x v.
  Proof.
    intros hind h hpre hgraph.
    induction hgraph as [x v | x P k v hP hh ih | x y k v w hy ihy hk ihk].
    all: cbn in *.
    - assumption.
    - apply ih. all: eauto.
    - destruct h as [hpy hv].
      apply ihk. 2: assumption.
      apply hv. apply ihy. 2: assumption.
      apply hind. assumption.
  Qed.

  Lemma funind_graph pre post x v :
    funind pre post →
    pre x →
    graph x v →
    post x v.
  Proof.
    intros h hpre hgraph.
    eapply orec_graph_inst_ind_step.
    all: eauto.
  Qed.

  Lemma def_ind pre post x h :
    funind pre post →
    pre x →
    post x (def x h).
  Proof.
    intros ho hpre.
    pose proof def_graph_sound.
    eapply funind_graph. all: eauto.
  Qed.

  (** Computing the domain, easier than using the graph *)

  Fixpoint comp_domain {a} (o : orec A B a) :=
    match o with
    | o_ret v => True
    | o_grd P k => P ∧ ∀ h, comp_domain (k h)
    | o_rec x k => domain x ∧ ∀ v, graph x v → comp_domain (k v)
    end.

  Lemma comp_domain_orec_domain a (o : orec A B (B a)) :
    comp_domain o →
    orec_domain o.
  Proof.
    intros h.
    induction o as [w | P k ih | x k ih] in h |- *.
    - eexists. constructor.
    - simpl in h. destruct h as [hP h].
      specialize (h hP). apply ih in h. destruct h as [w h].
      eexists. econstructor. eassumption.
    - simpl in h. destruct h as [[v hx] hk].
      specialize (hk v hx). apply ih in hk. destruct hk as [w h].
      eexists. econstructor. all: eassumption.
  Qed.

  Lemma compute_domain x :
    comp_domain (f x) →
    domain x.
  Proof.
    apply comp_domain_orec_domain.
  Qed.

  (* Now we can let it compute *)
  Transparent wf_partial.

End Fix.

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
  | o_ret v => p_ret v
  | o_grd P k => p_bind (guard P) (λ h, orec_apply (k h) f)
  | o_rec a k => p_bind (f a) (λ x, orec_apply (k x) f)
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

#[export] Instance Monad_orec {A B} : Monad (orec A B) := {|
  ret C c := o_ret c ;
  bind C D m k := orec_bind m k
|}.

(** Partial functions compose through orec *)

Definition o_lift {A B C} (u : partial C) : orec A B C :=
  o_grd (defined u) (λ h, o_ret (value u h)).

#[export] Instance Lift_partial_orec {A B} : MonadLift partial (orec A B) :=
  λ C u, o_lift u.

(** Tactics for functional induction *)

Lemma pfix_ind {A B} (f : ∀ x, orec A B (B x)) pre post a v :
  funind f pre post → pre a → pfix f a ↦ v → post a v.
Proof.
  intros hf hpre [hd ev].
  eapply funind_graph. 1,2: eassumption.
  rewrite <- (ev hd). exact (pfix_graph _ _ _ _ hd).
Qed.

Tactic Notation "funind" constr(p) "in" hyp(h) :=
  lazymatch type of h with
  | graph ?f ?x ?v =>
    lazymatch type of p with
    | context [ funind _ _ _ ] =>
      eapply funind_graph with (1 := p) in h ; [| try (exact I)]
    | _ => fail "Argument should be of type funind"
    end
  | _ => fail "Hypothesis should be about graph"
  end.

Tactic Notation "funind" constr(p) "in" hyp(h) "as" ident(na) :=
  lazymatch type of h with
  | graph ?f ?x ?v =>
    lazymatch type of p with
    | context [ funind _ _ _ ] =>
      eapply funind_graph with (1 := p) in h as na ; [| try (exact I)]
    | _ => fail "Argument should be of type funind"
    end
  | _ => fail "Hypothesis should be about graph"
  end.
