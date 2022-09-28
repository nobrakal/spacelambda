From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From glaneur.spacelang Require Import successors predecessors.
From glaneur.language Require Import language.

From glaneur Require Import more_maps_and_sets.
From glaneur Require Import interp.

Section Wp_call.

Context `{!interpGS Σ}.

Lemma zip_cons {A B} (x:A) (y:B) xs ys :
  zip (x::xs) (y::ys) = (x,y)::zip xs ys.
Proof. easy. Qed.

Lemma wp_call_later self args body ts vs b Q :
  length args = length vs →
  locs body = ∅ ->
  ts = tm_val <$> vs ->
  ▷ (wp b (substs' (zip (self::args) (val_code self args body::vs)) body) Q)
  ⊢ wp b (tm_call (val_code self args body) ts) Q.
Proof.
  iIntros (? ? ->) "Hspec".
  setoid_rewrite wp_unfold at 2.
  iIntros (? k σ) "Hi". simpl.
  iSplitR.
  { eauto using reducible_call. }
  iModIntro. iIntros (t' σ') "%Hstep".

  (* Invert the step *)
  apply invert_step_call in Hstep.
  destruct Hstep as (Hgc&?). subst.

  do 2 iModIntro.
  iSplitL "Hi".
  { iApply (@interp_weak _ _ _ _ _ (locs vs)).
    { pose proof (locs_substs' (zip (self :: args) (val_code self args body :: vs)) body) as Hlocs.
      rewrite zip_cons fmap_cons snd_zip in Hlocs; last lia.
      set_solver. }
    iApply interp_gc.
    { apply Hgc. }
    auto_locs. rewrite left_id_L. iFrame. }
  { by iApply "Hspec". }
Qed.

Lemma wp_call self args body ts vs b Q :
  length args = length vs →
  locs body = ∅ ->
  ts = tm_val <$> vs ->
  (wp b (substs' (zip (self::args) (val_code self args body::vs)) body) Q)
  ⊢ wp b (tm_call (val_code self args body) ts) Q.
Proof.
  iIntros. iApply wp_call_later; eauto.
Qed.

End Wp_call.
