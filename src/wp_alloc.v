From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.

From spacelambda.fracz Require Import qz qz_cmra.
From spacelambda Require Import more_maps_and_sets.
From spacelambda Require Import interp.

Section Wp_alloc.

Context `{!interpGS Σ}.

Lemma ugfrac_le (γ : gname) (m n : ugfrac) :
    @own Σ (authR (ugfracUR)) _ γ (● m) -∗
    @own Σ (authR (ugfracUR)) _  γ (◯ n) -∗
    ⌜(n ≤ m)%Qz⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as "%E".
  iPureIntro. apply auth_both_valid_discrete in E. destruct E.
  now apply ugfrac_included.
Qed.

Lemma ugfrac_remove (γ : gname) (m n : ugfrac) :
  @own Σ (authR (ugfracUR)) _ γ (● m) -∗
  @own Σ (authR (ugfracUR)) _  γ (◯ n) ==∗
  @own Σ (authR (ugfracUR)) _  γ (● (m - n : ugfrac)%Qz).
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as "%E".
  apply auth_both_valid_discrete in E. destruct E.
  iApply (own_update_2 with "Ha Hf").
  apply auth_update_dealloc.
  apply ugfrac_local_update.
  rewrite right_id.
  symmetry. apply Qz_sub_add.
  now apply ugfrac_included.
Qed.

Lemma exploit_diamonds b maxsize k σ L (n:nat) :
  interp b maxsize k σ L ∗ ♢ n ⊢
  ⌜reducible maxsize (dom k) (tm_alloc (tm_val (val_nat n))) σ⌝.
Proof.
  iIntros "[Hi Hpay]".
  destruct_interp "Hi".
  iDestruct (ugfrac_le γdia with "[$] [$]") as "%Hv".
  iPureIntro.
  apply related_available in Hσθ.
  destruct Hσθ as (?, (Hgc&?)).
  eapply reducible_gc.
  { apply (gc_weak Hgc).
    set_solver.  }
  apply reducible_alloc.
  unfold available in *.
  assert (n ≤ (maxsize - size_heap θ)) by now apply nat_to_Qz_inj_le.
  lia.
Qed.

Lemma add_fresh_ctx l r :
  l ∉ r ->
  own γctx (● gset_to_gmap 1%Qp r) ==∗
      own γctx (● gset_to_gmap 1%Qp ({[l]} ∪ r)) ∗ Stackable l 1%Qp.
Proof.
  iIntros (?) "Hk".
  iDestruct (own_update with "Hk") as ">Hk".
  { apply auth_update_alloc.
    apply alloc_local_update.
    { apply not_elem_of_dom.
      by rewrite dom_gset_to_gmap. }
    { assert (✓ 1%Qp) as E; try easy. apply E. } }
  rewrite own_op. iDestruct "Hk" as "[? ?]".
  rewrite -gset_to_gmap_union_singleton.
  rewrite insert_empty.
  by iFrame.
Qed.

Lemma remove_diamonds (p q : ugfrac) :
  own γdia (● q) ∗ ♢ p ==∗ own γdia (● (q - p : ugfrac)%Qz).
Proof.
  iIntros "[Ha Hf]".
  iApply (ugfrac_remove with "[$] [$]").
Qed.

Lemma wp_alloc (n:nat) b :
  ♢ n -∗
  wp b (tm_alloc n)
    (fun v => ∃ l, ⌜v = val_loc l⌝ ∗
           l ↦ (BBlock (replicate n val_unit)) ∗
           l ↤ ∅ ∗
           Stackable l 1%Qp).
Proof.
  iIntros "Hdiamn".
  rewrite wp_unfold /wp_pre. simpl.
  iIntros (maxsize k σ) "Hi".
  iDestruct (exploit_diamonds with "[$]") as "%Hr".
  iSplitR.
  { by iPureIntro. }
  iModIntro. clear Hr.
  iIntros (t' σ') "%Hstep".

  (* Invert the step *)
  apply invert_step_alloc in Hstep.
  destruct Hstep as (l,(σ1,(?&?&?&?&Hgc))). subst.

  (* rewrite locs. *)
  auto_locs.

  (* perform a gc *)
  iDestruct (interp_gc with "[$]") as "Hi".
  { by rewrite right_id_L. }

  iModIntro.
  iAssert (|==> interp b maxsize k ( <[l:=BBlock (replicate n val_unit)]> σ1) {[l]} ∗ l↦BBlock (replicate n val_unit) ∗ l↤∅ ∗ Stackable l 1%Qp)%I with "[Hdiamn Hi]" as ">[? [? [? ?]]]".
  { destruct_interp "Hi".

    rewrite right_id_L in Hσθ.

    assert (dom σ = dom σ1) as Hdσσ1 by eauto using gc_dom.
    assert (dom σ1 = dom θ) as Hdσ1θ by eauto using related_dom.

    assert (σ1 !! l = None).
    { apply not_elem_of_dom.
      rewrite -Hdσσ1.
      by apply not_elem_of_dom. }
    assert (θ !! l = None).
    { apply not_elem_of_dom.
      rewrite -Hdσ1θ -Hdσσ1.
      by apply not_elem_of_dom. }

    iAssert (interpret []) as "?".
    { by rewrite interpret_nil. }

    iMod (ph_alloc with "[$]") as "[? [? ?]]"; last iFrame.
    1,2:easy.
    { simpl. rewrite block_pointer_set_new_block. easy. }

    iMod (add_fresh_ctx l with "[$]") as "[? ?]".
    { by apply not_elem_of_dom. }
    iFrame.

    iDestruct (ugfrac_le with "[$] [$]") as "%Hav".
    apply nat_to_Qz_inj_le in Hav.
    iMod (remove_diamonds with "[$]") as "?".

    iExists (<[l:=BBlock (replicate n val_unit)]> θ). simpl.
    iFrame.

    rewrite dom_insert_L.
    repeat rewrite Hdσ1θ.
    iFrame.

    rewrite available_alloc; try easy.
    simpl. rewrite replicate_length.
    rewrite nat_to_Qz_sub //.
    iFrame.

    iPureIntro.

    split_and !; eauto.
    { eapply alloc_preserves_correct; eauto.
      eapply (correct_weak Hσ); set_solver. }
    { eapply alloc_preserves_correct; eauto.
      eapply (correct_weak Hθ); set_solver. }
    { eapply valid_store_alloc; eauto.
      simpl. rewrite replicate_length. unfold valid_store, available in *. lia. }
    now apply alloc_preserves_related. }
  iModIntro.
  iFrame. auto_locs.
  rewrite wp_unfold /wp_pre. simpl.
  iIntros. iFrame. iIntros. auto_locs. iFrame.
  iModIntro. iExists _. iFrame. easy.
Qed.

End Wp_alloc.
