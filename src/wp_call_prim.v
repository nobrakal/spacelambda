From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.

From spacelambda Require Import more_maps_and_sets.
From spacelambda Require Import interp.

Section Wp_call_prim.

Context `{!interpGS Σ}.

Lemma locs_result_eval_call_prim p vs x :
  eval_call_prim p vs = Some x ->
  locs_val x = ∅.
Proof.
  intros E.
  destruct p.
  (* XXX tactic, see invert_step *)
  all: destruct vs as [|?v ?vs]; simpl in E; try congruence.
  all: try destruct b; try congruence.
  all: destruct vs as [|?v ?vs]; simpl in E; try congruence.
  all: destruct v; try congruence.
  all: try destruct v0; try congruence.
  all: try destruct vs; try congruence.
  all: injection E; intros <-; auto_locs; set_solver.
Qed.

Lemma wp_call_prim b (p:prim) (vs:list val) w :
  eval_call_prim p vs = Some w ->
  ⊢ wp b (tm_call p (tm_val <$> vs)) (fun v => ⌜v = w⌝).
Proof.
  iIntros (Hw).
  rewrite wp_unfold /wp_pre. simpl.
  iIntros.
  iSplitR.
  { eauto using reducible_prim. }

  iModIntro.
  iIntros (? ?) "%Hstep".
  destruct (invert_step_call_prim _ Hstep) as (Hgc&(?,(?&Hv))). subst.

  iDestruct (interp_gc with "[$]") as "?".
  { apply (gc_weak Hgc).
    auto_locs. set_solver. }

  auto_locs. rewrite left_id_L.

  iDestruct (interp_weak with "[$]") as  "?"; last iFrame.
  { erewrite locs_result_eval_call_prim; eauto. set_solver. }
  do 2 iModIntro.

  rewrite Hv in Hw. injection Hw. intros ->.
  iApply wp_val. eauto.
Qed.

End Wp_call_prim.
