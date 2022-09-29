From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import semantics_equivalence semantics language.
From spacelambda.fracz Require Import qz qz_cmra.
From spacelambda Require Import ph interp wp wps wp_adequacy_alt.

From stdpp Require Import relations.

(* ------------------------------------------------------------------------ *)
(* Definitions *)

Definition reducible maxsize t σ :=
  exists t' σ', gc_then_step' maxsize ∅ (t,σ) (t',σ').

Definition not_stuck maxsize t σ :=
  is_Some (to_val t) \/ reducible maxsize t σ.

Lemma not_stuck_impl maxsize t σ :
  wp_adequacy_alt.not_stuck maxsize t σ -> not_stuck maxsize t σ.
Proof.
  intros [? [|(?&?&?)]].
  { now left. }
  { right. eexists _,_. eapply gts_equiv_alt. eauto. }
Qed.

(* ------------------------------------------------------------------------ *)

Lemma wp_adequacy_partial_correctness t b maxsize v' σ' Q :
  locs t = ∅ ->
  rtc (reduction' maxsize) (t,∅) (tm_val v',σ') ->
  (∀ `{!interpGS Σ},
     ⊢ ♢maxsize -∗ wp b t (fun v => ⌜Q v⌝)) ->
  Q v'.
Proof.
  intros ? Hsteps ?.
  apply reduction_impl_gts in Hsteps.
  destruct Hsteps as [(?&?) | (?&?&?)]; subst;
    eapply wp_adequacy_partial_correctness; eauto;
    apply gts_equiv_alt'; now eauto.
Qed.

Lemma wp_adequacy_not_stuck t b maxsize t' σ' :
  locs t = ∅ ->
  rtc (reduction' maxsize) (t,∅) (t',σ') ->
  (∀ `{!interpGS Σ},
      ⊢ ♢maxsize -∗ wp b t (fun _ => ⌜ True ⌝)) ->
  not_stuck maxsize t' σ'. (* Here not_stuck means we can do a gc and a real step. *)
Proof.
  intros ? Hsteps ?.
  apply reduction_impl_gts in Hsteps.
  apply not_stuck_impl.
  destruct Hsteps as [(?&Hgc) | (?,(?&?))]; subst.
  {eapply wp_adequacy_not_stuck; eauto.
    apply gc_inv_empty in Hgc. subst. easy. }
  { eapply not_stuck_prepone; eauto.
    eapply wp_adequacy_not_stuck ; eauto.
     apply gts_equiv_alt'. eauto. }
Qed.

Lemma wp_adequacy maxsize b t t' σ' Q :
  locs t = ∅ ->
  rtc (reduction' maxsize) (t,∅) (t',σ') ->
  (∀ `{!interpGS Σ},
      ⊢ ♢maxsize -∗ wp b t (fun v => ⌜Q v⌝)) ->
  (exists v', t' = tm_val v' /\ Q v') \/ reducible maxsize t' σ'.
Proof.
  intros ? ? Hwp.
  destruct (to_val t') eqn:E.
  { destruct t'; try easy. injection E. intros ?. subst.
    left. eexists. split; try easy.
    eapply wp_adequacy_partial_correctness; eauto. }
  { right.
    edestruct wp_adequacy_not_stuck as [N|N]; eauto.
    { iIntros. iDestruct (Hwp with "[$]") as "?". iApply (wp_mono with "[$]"). eauto. }
    { rewrite E in N. inversion N. easy. } }
Qed.

(* ------------------------------------------------------------------------ *)
(* Adequacy for WPS with an empty souvenir. *)

Lemma simple_wps_adequacy (A:Type) (EA:Enc A) maxsize t t' σ' (Q : A -> Prop):
  locs t = ∅ ->
  rtc (reduction' maxsize) (t,∅) (t',σ') ->
  (∀ `{!interpGS Σ},
      ⊢ ♢maxsize -∗ wps (Some ∅) t (fun v => ⌜Q v⌝)) ->
  (exists v', t' = tm_val (enc v') /\ Q v') \/ reducible maxsize t' σ'.
Proof.
  intros ? ? Hwps.
  edestruct wp_adequacy
    with (Q:=fun v => ∃ a, v = enc a /\ Q a) as [(?,(?&(?,(?&?))))|?]; subst; eauto.
  iIntros.
  iDestruct (Hwps with "[$]") as "?".
  rewrite wps_eq.
  iDestruct (wpc_wp_empty with "[$]") as "?".
  rewrite wp_enc_eq.
  iApply (wp_mono with "[$]").
  iIntros (?) "[% [% %]]".
  eauto.
Qed.
