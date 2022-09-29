From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.

From spacelambda Require Import more_maps_and_sets more_space_lang.
From spacelambda Require Import interp.

Set Implicit Arguments.

Section Wp_store.

Context `{!interpGS Σ}.

Lemma wp_store (l:loc) (n:nat) v qv lsv vs b :
  (is_loc v -> qv <> 0%Qz) ->
  n < length vs ->
  l ↦ (BBlock vs) ∗ v ↤?{qv} lsv ⊢
    wp b (tm_store l n v)
    (fun tt => ⌜tt = val_unit⌝ ∗ l ↦ (BBlock (<[n:=v]> vs))
             ∗ v↤?{qv}(lsv ⊎ {[+ l +]})
             ∗ (vs !!! n)↤?{0}({[-l-]})).
Proof.
  iIntros (? Hvs) "[Hmapsto Hv]".

  rewrite wp_unfold /wp_pre. simpl.
  auto_locs. rewrite right_id_L.
  iIntros (? k σ) "Hi".
  iDestruct (exploit_mapsto with "[$]") as "%Hl".
  { set_solver. }

  iModIntro. iSplitR.
  { eauto using reducible_store. }

  iIntros (t' σ') "%Hstep".
  apply invert_step_store in Hstep.
  destruct Hstep as (σ1,( bs, (Hgc&Hbs&?&?))). subst.

  assert (bs = vs) as ->.
  { rewrite (gc_read_root _ Hgc Hl) in Hbs. { by injection Hbs. }
    set_solver. }

  iDestruct (interp_gc with "[$]") as "Hi".
  { apply (gc_weak Hgc). set_solver. }

  assert (exists w, vs !! n = Some w) as (w,Hw).
  { apply lookup_lt_is_Some. easy. }

  iModIntro.
  auto_locs.
  iAssert (|==> interp _ _ k (<[l:=BBlock (<[n:=v]> vs)]> σ1) ∅ ∗ l ↦ BBlock (<[n:=v]> vs) ∗ v↤?{qv}(lsv ⊎ {[+ l +]}) ∗ w↤?{0%Qz}({[-l-]}))%I with "[Hi Hmapsto Hv]" as ">[? [? [? ?]]]".
  { destruct_interp "Hi".

    assert (θ !! l = Some (BBlock vs)) as E.
    { eapply related_read_root.
      2:{ apply related_symmetric. apply Hσθ. }
      { set_solver. }
      eapply gc_read_root.
      2:{ apply Hgc. }
      { set_solver. }
      easy. }

    iDestruct (ph_store_heap with "[$]") as ">[Hi [? [? ?]]]".
    1-4:eauto.
    lia.

    iModIntro. iFrame.
    iExists (<[l:=BBlock (<[n:=v]> vs)]> θ). iFrame.
    rewrite (available_update _ _ _ _ _ E).
    2:{ eauto using size_block_update. }

    rewrite dom_insert_L.
    assert ({[l]} ∪ dom σ1 = dom σ1) as ->.
    { assert (l ∈ dom σ1) by (now apply elem_of_dom). set_solver. }
    iFrame.

    iPureIntro. rewrite right_id_L.
    split_and !.
    { eapply correct_weak.
      { apply update_preserves_correct with w.
        5:apply Hσ. all: try easy; set_solver. }
      set_solver. }
    { eapply correct_weak.
     { apply update_preserves_correct with w.
        5:apply Hθ. all: try easy; set_solver. }
     set_solver. }
    { eapply valid_store_update; eauto.
      rewrite size_block_update. unfold valid_store in *. simpl in *. lia. }
    { eapply related_weak.
      { eapply update_preserves_related with w.
        3:apply Hσ.
        all:try easy; set_solver. }
    set_solver. } }
  iModIntro. iFrame.
  rewrite wp_unfold /wp_pre.
  iIntros.
  iFrame.
  replace (vs !!! n) with w. by iFrame.
  rewrite list_lookup_total_alt Hw //.
Qed.

End Wp_store.
