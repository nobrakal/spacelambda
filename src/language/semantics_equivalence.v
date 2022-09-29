Require Import Coq.Program.Equality.

From stdpp Require Import base sets relations gmap.
From spacelambda.language Require Import head_semantics semantics alt_semantics gc.

(* ------------------------------------------------------------------------ *)
(* We enunciate the equivalence between [reduction] and [alt_reduction]
   using the [gc_then_step] relation. *)

Inductive gc_then_step :
  nat -> gset loc ->
  tm → store →
  tm → store → Prop :=
| GCHeadStep maxsize r t1 σ1 σ1' t2 σ2 :
  gc (r ∪ locs t1) σ1 σ1' →
  step maxsize t1 σ1' t2 σ2 →
  gc_then_step maxsize r t1 σ1 t2 σ2.

(* A curryfied version. *)
Definition gc_then_step' maxsize r : relation (tm * store) :=
  fun '(t1,σ1) '(t2,σ2) => gc_then_step maxsize r t1 σ1 t2 σ2.

(* ------------------------------------------------------------------------ *)
(* We need deep contexts *)

Definition fill_deep ctxs t : tm :=
  List.fold_right fill_item t ctxs.

Lemma fill_deep_app_eq ctxs1 ctxs2 t :
  fill_deep (ctxs1 ++ ctxs2) t = fill_deep ctxs1 (fill_deep ctxs2 t).
Proof.
  revert ctxs2 t.
  induction ctxs1; intros ctxs2 t; simpl; try easy.
  by rewrite IHctxs1.
Qed.

Lemma locs_cons_eq E ctxs :
  locs (E::ctxs) = locs_ctx E ∪ locs ctxs.
Proof. easy. Qed.

Lemma locs_app_eq ctxs1 ctxs2 :
  locs (ctxs1 ++ ctxs2) = locs ctxs1 ∪ locs ctxs2.
Proof.
  revert ctxs2.
  induction ctxs1; intros ctxs2; simpl.
  { set_solver. }
  { repeat rewrite locs_cons_eq.
    rewrite IHctxs1. set_solver. }
Qed.

Lemma locs_fill_deep_eq ctxs t :
  locs_tm (fill_deep ctxs t) = locs ctxs ∪ locs_tm t.
Proof.
  revert t.
  induction ctxs; simpl; intros t.
  { set_solver. }
  { rewrite locs_cons_eq.
    rewrite locs_fill_item.
    rewrite IHctxs.
    set_solver. }
Qed.

Lemma distant_ctx maxsize ctxs t1 σ1 t2 σ2 :
  head_step maxsize t1 σ1 t2 σ2 ->
  step maxsize (fill_deep ctxs t1) σ1 (fill_deep ctxs t2) σ2.
Proof.
  revert t1 σ1 t2 σ2.
  induction ctxs; intros t1 σ1 t2 σ2 He.
  { now eapply StepHead. }
  { simpl. eapply StepCtx; try easy.
    by eapply IHctxs. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Implication alt_reduction -> gc_then_step *)

Lemma alt_impl_gts_aux maxsize r ctxs t1 σ1 t2 σ2 :
  alt_reduction maxsize (r ∪ locs ctxs) t1 σ1 t2 σ2 ->
  gc_then_step maxsize r (fill_deep ctxs t1) σ1 (fill_deep ctxs t2) σ2.
Proof.
  intros Hdgs.
  dependent induction Hdgs; subst.
  { specialize IHHdgs with r (ctxs++[E]).
    repeat rewrite fill_deep_app_eq in IHHdgs. simpl in *.
    apply IHHdgs. rewrite locs_app_eq. set_solver. }
  { econstructor.
    { rewrite locs_fill_deep_eq.
      by rewrite union_assoc_L. }
    { by eapply distant_ctx. } }
Qed.

Theorem alt_impl_gts maxsize r t1 σ1 t2 σ2 :
  alt_reduction maxsize r t1 σ1 t2 σ2 ->
  gc_then_step maxsize r t1 σ1 t2 σ2.
Proof.
  intros.
  apply (alt_impl_gts_aux _ r nil).
  rewrite right_id_L; try apply _.
  easy.
Qed.

(* ------------------------------------------------------------------------ *)
(* Implication gc_then_step -> alt_reduction *)

Lemma distant_gc_ctxs maxsize E ctxs t1 σ1 σ1' t2 σ2 :
  gc (E ∪ locs ctxs ∪ locs_tm t1) σ1 σ1' ->
  head_step maxsize t1 σ1' t2 σ2 ->
  alt_reduction maxsize E (fill_deep ctxs t1) σ1 (fill_deep ctxs t2) σ2.
Proof.
  revert E t1 σ1 σ1' t2 σ2.
  induction ctxs; intros E t1 σ1 σ1' t2 σ2; intros Hgc Hds; simpl in *.
  { eapply AltRedGCHead; try (apply Hds).
    eapply gc_weak; try (apply Hgc).
    set_solver. }
  { rewrite locs_cons_eq in Hgc.
    eapply AltRedCtx; try easy.
    eapply IHctxs; try (apply Hds).
    eapply gc_weak; try (apply Hgc).
    rewrite union_assoc_L.
    set_solver. }
Qed.

Lemma step_inv maxsize t1 σ1 t2 σ2 :
  step maxsize t1 σ1 t2 σ2 ->
  exists ctxs t1' t2',
    head_step maxsize t1' σ1 t2' σ2
    /\ t1 = fill_deep ctxs t1'
    /\ t2 = fill_deep ctxs t2'.
Proof.
  intros Hds.
  dependent induction Hds.
  { destruct IHHds as (ctxs,(t1'', (t2'',(?&?&?)))).
    subst.
    exists (E::ctxs), t1'', t2''. easy. }
  { exists nil, t1, t2. easy. }
Qed.

Lemma gts_impl_alt maxsize r t1 σ1 t2 σ2 :
  gc_then_step maxsize r t1 σ1 t2 σ2 ->
  alt_reduction maxsize r t1 σ1 t2 σ2.
Proof.
  intros Hgc.
  inversion Hgc; clear Hgc; subst.
  apply step_inv in H0.
  destruct H0 as (?&?&?&?&?&?). subst.
  eapply distant_gc_ctxs; try (apply H1).
  { apply (gc_weak H).
    rewrite locs_fill_deep_eq.
    set_solver. }
  easy.
Qed.

(* ------------------------------------------------------------------------ *)
(* Summarize what we proved *)

Lemma gts_equiv_alt maxsize r t1 σ1 t2 σ2 :
  gc_then_step maxsize r t1 σ1 t2 σ2 <-> alt_reduction maxsize r t1 σ1 t2 σ2.
Proof.
  split; eauto using gts_impl_alt, alt_impl_gts.
Qed.

Lemma gts_equiv_alt' maxsize r t1 σ1 t2 σ2 :
  rtc (gc_then_step' maxsize r) (t1,σ1) (t2,σ2) <-> rtc (alt_reduction' maxsize r) (t1,σ1) (t2,σ2).
Proof.
  split; intros Hrtc;
    (eapply rtc_subrel; [ | apply Hrtc]);
    intros [] []; eapply gts_equiv_alt.
Qed.


(* ------------------------------------------------------------------------ *)
(* Now the equivalence between [reduction] and [gc_then_step].
   The equivalence concerns the whole derivation. *)

Lemma reduction_impl_gts_pre maxsize t1 σ1 t2 σ2 :
  rtc (reduction' maxsize )  (t1,σ1) (t2,σ2) ->
  ( t1=t2 /\ gc (locs t2) σ1 σ2 ) \/
  ( ∃ t' σ' σ2',
     gc_then_step' maxsize ∅ (t1,σ1) (t',σ') /\ gc (locs t2) σ2' σ2 /\ rtc (gc_then_step' maxsize ∅) (t',σ') (t2,σ2')).
Proof.
  intros Hrtc.
  dependent induction Hrtc.
  { left. split; try easy.
    apply gc_id. }
  destruct y as (t1', σ1').
  specialize (IHHrtc t1' σ1' t2 σ2 eq_refl eq_refl).
  clear Hrtc.
  destruct IHHrtc as [IH | IH].
  { destruct IH as (?&?). subst.
    inversion H; subst.
    { right. eexists _,_,_.
      split; last split.
      { eapply GCHeadStep; eauto using gc_id. }
      { eauto. }
      easy.  }
    { left. eauto using gc_trans. } }
  { right.
    destruct IH as (t',(σ', (σ2', ( Headgc & Hgc & ?)))).
    inversion H; subst.
    { eexists _,_,_.
      split; last split.
      2:apply Hgc.
      { eapply GCHeadStep.
        { apply gc_id. }
        { eauto. } }
      { eauto using rtc_l. } }
    { eexists _,_,_.
      inversion Headgc; subst.
      split; last split.
      { econstructor.
        { rewrite left_id_L in *. 2,3:apply _.
          eapply gc_trans with (σ2:=σ1'); eauto. }
        { eauto. } }
      all:eauto. } }
Qed.

(* Having the rtc of reduction means either
   1) We did only GCs
   2) We alternated distant steps and GCs, and at the end a GC. *)
Lemma reduction_impl_gts maxsize t1 σ1 t2 σ2 :
  rtc (reduction' maxsize)  (t1,σ1) (t2,σ2) ->
  ( t1=t2 /\ gc (locs t2) σ1 σ2 ) \/
  ( ∃ σ2', gc (locs t2) σ2' σ2 /\ rtc (gc_then_step' maxsize ∅) (t1,σ1) (t2,σ2')).
Proof.
  intros Hrtc.
  apply reduction_impl_gts_pre in Hrtc.
  destruct Hrtc as [| (t',(σ1',(σ2',(? & ? & ?))))].
  { eauto. }
  { right. eexists σ2'.
    split; try easy.
    eauto using rtc_l. }
Qed.

Lemma gts_impl_reduction maxsize t1 σ1 t2 σ2 :
  rtc (gc_then_step' maxsize ∅) (t1,σ1) (t2,σ2) ->
  rtc (reduction' maxsize)       (t1,σ1) (t2,σ2).
Proof.
  intros Hrtc.
  dependent induction Hrtc.
  { easy. }
  { destruct y. inversion H; subst.
    eapply rtc_l with (y:=(t1,σ1')).
    { eapply RedGC. rewrite left_id_L in H0; last apply _.
      eauto. }
    eapply rtc_l; last eauto using IHHrtc.
    now eapply RedStep. }
Qed.
