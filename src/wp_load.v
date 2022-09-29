From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.

From spacelambda Require Import more_maps_and_sets.
From spacelambda Require Import interp.

Set Implicit Arguments.

Section Wp_load.

Context `{!interpGS Σ}.

Lemma wp_load (l:loc) (n:nat) q vs b :
  n < length vs ->
  l ↦{q} (BBlock vs) ⊢
    wp b (tm_load l n)
    (fun v => l ↦{q} (BBlock vs) ∗ ⌜v = vs !!! n⌝).
Proof.
  iIntros (?) "Hmapsto".
  rewrite wp_unfold /wp_pre. simpl.
  iIntros (? ? ?) "Hi".

  iDestruct (exploit_mapsto with "[$]") as "%Hl".
  { auto_locs. set_solver. }

  iSplitR.
  { eauto using reducible_load. }
  iModIntro.

  iIntros (? ?) "%Hstep".
  apply invert_step_load in Hstep.
  destruct Hstep as (Hgc&(bs,(v,(Hload&?&Hn)))). subst.

  auto_locs. rewrite right_id_L.
  iDestruct (interp_gc with "[$]") as "Hi".
  { apply Hgc. }

  do 2 iModIntro.

  iSplitL "Hi".
  { destruct_interp "Hi".
    iExists θ. iFrame.
    iPureIntro.

    assert (θ !! l = Some (BBlock bs)).
    { erewrite related_read_root.
      3:{ apply related_symmetric, Hσθ. }
      all: try easy.
      set_solver. }

    pose (locs_elem_subseteq _ _ _ Hn).
    split_and !; eauto.
    { eapply (@correct_inline_root l bs) in Hσ; try easy.
      apply (correct_weak Hσ). all:set_solver. }
    { eapply (@correct_inline_root l bs) in Hθ; try easy.
      apply (correct_weak Hθ). all:set_solver. }
    apply (@related_inline_block_root l bs) in Hσθ.
    eapply (related_weak Hσθ).
    all: try easy; set_solver. }
  { rewrite wp_unfold /wp_pre. simpl.
    iIntros. iFrame. iPureIntro.
    assert (l ∈ (dom k ∪ {[l]})) as Hkl by set_solver.
    erewrite (gc_read_root Hkl Hgc Hl) in Hload.
    injection Hload. intros ->.
    rewrite (list_lookup_total_alt bs n) Hn.
    easy. }
Qed.

End Wp_load.
