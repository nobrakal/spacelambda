From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From glaneur.fracz Require Import qz qz_cmra smultiset_cmra.
From glaneur.language Require Import notation closure.
From glaneur Require Import interp.

From glaneur Require Import utils more_space_lang wp_all wp_spec wps triple.

From glaneur.examples.tactics Require Import tactics.
From glaneur.examples.lib Require Import ref.

Definition swap x y : tm :=
  let: "a" := get [[x]] in
  let: "b" := get [[y]] in
  set [[x, "b"]];;
  set [[y, "a"]].

Definition mk_swap : val :=
  λ: [[]], mk_clo BAnon [BNamed "x"; BNamed "y"] (swap "x" "y").

Definition call_swap l x y : tm :=
  call_clo l [x;y].

Section Swap.
Context `{!interpGS Σ}.

Definition swap_spec_1 (vs:list val) (t:tm) (spec:iProp Σ) : iProp Σ :=
  ∀ (x y:loc) (a b:nat), ⌜vs = [val_loc x; val_loc y]⌝ ∗ isRef a x ∗ isRef b y -∗
     wps None t (fun _ => isRef b x ∗ isRef a y ∗ spec).

Definition swap_spec_2 (vs:list val) (t:tm) (spec:iProp Σ) : iProp Σ :=
  ∀ (x:loc) (a:nat), ⌜vs = [val_loc x; val_loc x]⌝ ∗ isRef a x -∗
     wps None t (fun _ => isRef a x ∗ spec).

Definition swap_spec (_:loc) (vs:list val) (t:tm) (spec:iProp Σ) : iProp Σ :=
  swap_spec_1 vs t spec ∧ swap_spec_2 vs t spec.

Local Instance lne_spawn_spec_1 : LNE swap_spec.
Proof.
  lne_pre tt.
  intros ? ? ? ? ? ? ?. f_equiv.
  { unfold swap_spec_1. repeat f_equiv; eauto. }
  { unfold swap_spec_2. repeat f_equiv; eauto. }
Qed.

Lemma mk_counter_spec :
  CODE (mk_swap [])
  PRE (♢ 1)
  POST (fun l:loc => l ↤ ∅ ∗ Stackable l 1%Qp ∗ Spec 2 nil swap_spec l).
Proof.
  wps_call. iSplitR; eauto.
  wps_nofree.
  wps_apply (wps_mk_spec swap_spec nil nil ).
  1-4:compute_done.
  { iModIntro. iIntros. simpl.
    do 2 (destruct vs as [|? ?vs] ; simpl in *; try congruence).
    iSplit.
    { iIntros (? ? ? ?) "(%Eq & ? & ?)".
      injection Eq; intros -> -> ->.
      wps_bind. wps_apply @get_spec as "(% & ?)".
      wps_bind. wps_apply @get_spec as "(% & ?)". subst.
      wps_bind. wps_apply @set_spec_no_loc. easy. simpl.
      wps_apply @set_spec_no_loc. easy.
      by iFrame. }
    { iIntros (? ?) "(%Eq & ?)".
      injection Eq; intros -> -> ->.
      wps_bind. wps_apply @get_spec as "(% & ?)".
      wps_bind. wps_apply @get_spec as "(% & ?)". subst.
      wps_bind. wps_apply @set_spec_no_loc. easy. simpl.
      wps_apply @set_spec_no_loc. easy. iFrame. } }
  simpl. iSplitL. rewrite right_id_L. simpl.  rewrite /group_pointedbys. simpl.
  by iFrame.
  iIntros. by iFrame.
Qed.


Lemma call_swap_spec l x y (a b:nat) :
  CODE (call_swap l x y)
  PRE (isRef a x ∗ isRef b y ∗ Spec 2 nil swap_spec l)
  POST (fun _ => isRef a y ∗ isRef b x ∗ Spec 2 nil swap_spec l).
Proof.
  iIntros "(? & ? & ?)".
  wps_call. iFrame.
  iIntros (?) "E".
  iDestruct "E" as "[E _]".
  rewrite /swap_spec_1.
  wps_nofree.
  iApply (wps_mono with "[-]").
  iApply ("E" $! x y). by iFrame.
  iIntros (_) "(? & ? & ?)". by iFrame.
Qed.
End Swap.
