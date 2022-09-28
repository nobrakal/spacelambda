From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import auth.
From stdpp Require Import gmap gmultiset.

From glaneur.spacelang Require Import successors predecessors.
From glaneur.language Require Import semantics_equivalence semantics language.
From glaneur.fracz Require Import qz qz_cmra.
From glaneur Require Import ph interp wp.

From stdpp Require Import relations.

(* [step] is a sugar for alt_reduction *)
Definition step maxsize r := fun '(t,σ) '(t',σ') => alt_reduction maxsize r t σ t' σ'.

(* [not_stuck_pre r t σ] expresses that [t] is either a value,
   or reduce with a store σ and roots r *)
Definition not_stuck_pre maxsize r t σ :=
  correct (r ∪ locs t) σ  /\ ((is_Some (to_val t)) \/ (reducible maxsize r t σ)).

(* ------------------------------------------------------------------------ *)
(* Pre_adequacy *)

Section pre_adequacy.
Context `{iG:!interpGS Σ}.

Lemma wp_adequacy_not_stuck_pre b maxsize k t σ Q :
  interp b maxsize k σ (locs t) ∗ wp b t Q -∗
  ⌜not_stuck_pre maxsize (dom _ k) t σ⌝.
Proof.
  iIntros "[Hi Hwp]".
  rewrite wp_unfold /wp_pre.
  iAssert (⌜correct (dom _ k ∪ locs t) σ⌝)%I with "[-]" as "%E".
  { destruct_interp "Hi". eauto. }

  destruct (to_val t) eqn:?.
  { iPureIntro. split; try easy. eauto. }

  iMod ("Hwp" with "[$]") as "[%Hred Hwp]".
  iPureIntro. split; try easy. eauto.
Qed.

Lemma wp_adequacy_pre b maxsize k n t σ t' σ' Q :
  nsteps (step maxsize (dom _ k)) n (t,σ) (t',σ') ->
  interp b maxsize k σ (locs t) ∗ wp b t Q -∗ |={∅}▷=>^(n)
  interp b maxsize k σ' (locs t') ∗ wp b t' Q.
Proof.
  revert k t σ t' σ' Q.
  induction n; intros k t σ t' σ' Q;
    inversion_clear 1;
    iIntros "[Hi Hwp]".
  { by iFrame. }
  { destruct y as (t1,σ1).
    rewrite wp_unfold /wp_pre. simpl.
    unfold step in *.
    rewrite (alt_reduction_no_val H0).
    iMod ("Hwp" with "[$]") as "[_ Hwp]". simpl.
    do 2 iModIntro. iMod ("Hwp" with "[%]") as "[? ?]".
    { apply H0. }
    iModIntro.
    iApply IHn.
    { apply H1. }
    iFrame. }
Qed.

Lemma wp_adequacy_not_stuck_iterated b maxsize n k t σ t' σ' Q :
  nsteps (step maxsize (dom _ k)) n (t,σ) (t',σ') ->
  interp b maxsize k σ (locs t) ∗ wp b t Q -∗
  |={∅}▷=>^(S n)  ⌜not_stuck_pre maxsize (dom _ k) t' σ'⌝.
Proof.
  iIntros (Hsteps) "?".
  iDestruct (wp_adequacy_pre with "[$]") as "?".
  { apply Hsteps. }
  iApply (step_fupdN_mono with "[$]").
  iIntros. iApply wp_adequacy_not_stuck_pre.
  iFrame.
Qed.

End pre_adequacy.

(* ------------------------------------------------------------------------ *)
(* not_stuck *)

Definition not_stuck maxsize := not_stuck_pre maxsize ∅.

Lemma not_stuck_prepone maxsize t σ σ' :
  gc (locs t) σ' σ ->
  not_stuck maxsize t σ' ->
  not_stuck maxsize t σ.
Proof.
  intros Hgc [Hcor Hs].
  assert (correct (∅ ∪ locs t) σ).
  { eapply gc_preserves_correct; eauto. now rewrite left_id_L. }
  destruct Hs; split; eauto.
  right. eapply reducible_prepone; eauto.
  destruct Hcor; eauto.
  rewrite left_id_L; eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Initialization *)

Import Initialization.

(* steps is the reflexive-transitive closure of step in the empty
   context. *)
Definition steps maxsize := rtc (step maxsize ∅).

Lemma wp_adequacy_open Σ `{!interpPreG Σ} b t maxsize v' σ' Q :
  locs t = ∅ ->
  steps maxsize (t,∅) (tm_val v',σ') ->
  (∀ `{!interpGS Σ},
     ⊢ ♢maxsize -∗ wp b t (fun v => ⌜Q v⌝)) ->
  Q v'.
Proof.
  intros Hlt Hsteps Hwp.

  apply rtc_nsteps in Hsteps.
  destruct Hsteps as (n,Hsteps).

  apply (step_fupdN_soundness _ (S n)). iIntros.

  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hinv".

  iMod (interp_init b maxsize) as "[%HinterpGS [%He [Hi Hdia]]]".
  iDestruct (Hwp HinterpGS) as "Hwp".
  iSpecialize ("Hwp" with "[$]").
  rewrite -Hlt.
  iDestruct (@wp_adequacy_pre _ _ with "[$]") as "Hadequate".
  { rewrite dom_empty_L. apply Hsteps. }
  iApply (@step_fupdN_mono _ _ _ _ (S n) with "[Hadequate]").
  2:{ simpl. repeat rewrite He. by iFrame. }
  iIntros "[? Hwp]".
  rewrite wp_unfold /wp_pre. iMod ("Hwp" with "[$]") as "[? ?]".
  iFrame.
Qed.

Lemma wp_adequacy_not_stuck_open `{!interpPreG Σ} b t maxsize t' σ' Q :
  locs t = ∅ ->
  steps maxsize (t,∅) (t',σ') ->
  (∀ `{!interpGS Σ},
      ⊢ ♢maxsize -∗ wp b t Q) ->
  not_stuck maxsize t' σ'.
Proof.
  intros Hlt Hsteps Hwp.

  apply rtc_nsteps in Hsteps.
  destruct Hsteps as (n,Hsteps).

  apply (step_fupdN_soundness _ (S n)). iIntros.

  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hinv".

  iMod (interp_init b maxsize) as "[%HinterpGS [%He [Hi Hdia]]]".
  iDestruct (Hwp HinterpGS) as "Hwp".
  iSpecialize ("Hwp" with "[$]").
  rewrite -Hlt.
  iDestruct (@wp_adequacy_not_stuck_iterated _ _ with "[$]") as "Hadequate".
  { rewrite dom_empty_L. apply Hsteps. }
  iApply (@step_fupdN_mono _ _ _ _ (S n) with "[Hadequate]").
  2:{ simpl. repeat rewrite He. by iFrame. }
  rewrite dom_empty_L. by iFrame.
Qed.

Lemma wp_adequacy_partial_correctness t b maxsize v' σ' Q :
  locs t = ∅ ->
  steps maxsize (t,∅) (tm_val v',σ') ->
  (∀ `{!interpGS Σ},
     ⊢ ♢maxsize -∗ wp b t (fun v => ⌜Q v⌝)) ->
  Q v'.
Proof.
  intros.
  eapply wp_adequacy_open; eauto with typeclass_instances.
Qed.

Lemma wp_adequacy_not_stuck b t maxsize t' σ' :
  locs t = ∅ ->
  steps maxsize (t,∅) (t',σ') ->
  (∀ `{!interpGS Σ},
      ⊢ ♢maxsize -∗ wp b t (fun _ => ⌜ True ⌝)) ->
  not_stuck maxsize t' σ'.
Proof.
  intros.
  eapply wp_adequacy_not_stuck_open; eauto with typeclass_instances.
Qed.
