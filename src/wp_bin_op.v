From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From glaneur.spacelang Require Import successors predecessors.
From glaneur.language Require Import language.

From glaneur Require Import more_maps_and_sets.
From glaneur Require Import interp.

Section Wp_bin_op.

Context `{!interpGS Σ}.

Lemma wp_bin_op op (n m:nat) b :
  ⊢ wp b (tm_bin_op op n m) (fun v => ⌜v = val_nat (exec_bin_op op n m)⌝).
Proof.
  iStartProof.
  rewrite wp_unfold /wp_pre. simpl.
  iIntros.
  iSplitR.
  { eauto using reducible_bin_op. }

  iModIntro.
  iIntros (? ?) "%Hstep".
  destruct (invert_step_bin_op Hstep) as (Hgc&?). subst.

  iDestruct (interp_gc with "[$]") as "?".
  { apply (gc_weak Hgc). set_solver. }

  auto_locs. rewrite left_id_L.
  do 2 iModIntro.
  iFrame.

  rewrite wp_unfold /wp_pre.
  simpl. iIntros. iFrame.
  eauto.
Qed.

End Wp_bin_op.
