From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From glaneur.fracz Require Import qz qz_cmra smultiset_cmra.
From glaneur.language Require Import notation closure.
From glaneur Require Import interp.

From glaneur Require Import utils more_space_lang wp_all wp_spec wps triple.

From glaneur.examples.tactics Require Import tactics.
From glaneur.examples.lib Require Import ref.
From glaneur.examples.counter Require Import counter.

Definition mk_counter_both : val :=
  λ: [[]],
    let: "r" := ref [[0]] in
    mk_clo BAnon [] (incr [["r"]];; get [["r"]]).

Section CounterIncrAndGet.
  Context `{interpGS Σ}.

Definition incr_and_get_clo_spec (r l:loc) (_:list val) (t:tm) (spec:iProp Σ) : iProp Σ :=
  ∀ (n:nat), isRef n r -∗ wps (Some {[r]}) t (fun m => ⌜m=(1+n)%nat⌝ ∗ isRef (1+n) r ∗ spec).
Local Instance lne_incr_and_get_clo_spec r : LNE (incr_and_get_clo_spec r).
Proof. lne. Qed.

Lemma prove_incr_and_get r (l : loc) (vs : list val) :
  length vs = 0 ->
  Spec 0 [((#r)%V, 1%Qz)] (incr_and_get_clo_spec r) l -∗
  incr_and_get_clo_spec r l vs (incr [[#r]] ;; get [[#r]]) (Spec 0 [((#r)%V, 1%Qz)] (incr_and_get_clo_spec r) l).
Proof.
  iIntros.

  unfold incr_and_get_clo_spec.
  iIntros.
  wps_bind.
  wps_apply incr_spec.

  wps_nofree.
  iDestruct (@get_spec_enc with "[$]") as "Hget".
  iApply (@wps_mono with "[$]").
  iIntros (?) "[%Hv ?]". subst.
  iStepsS.
Qed.

(* The actual counter representation predicate. *)
Definition IsCounterIncrAndGet (n:nat) (f:loc) : iProp Σ :=
  ∃ r, isRef n r ∗ Stackable r 1%Qp ∗ Spec 0 [((#r)%V,1%Qz)] (incr_and_get_clo_spec r) f.

Lemma mk_counter_both_spec :
  ♢ 3 -∗
  wps (Some ∅) (mk_counter_both [])
  (fun f => Stackable f 1%Qp ∗ f ↤ ∅ ∗ IsCounterIncrAndGet 0 f).
Proof.
  iIntros.
  wps_call.
  wps_nofree.

  wps_bind_nofree.
  mine 2.
  wps_apply ref_spec_no_loc as (r) "(Hr & ? & ?)"; first easy.

  wps_apply (wps_mk_spec (incr_and_get_clo_spec r) [("r", val_loc r)] [1%Qz]).
  1-4:compute_done.
  { iModIntro. simpl. iIntros. iApply prove_incr_and_get; eauto. }
  simpl. rew_qz.
  iStepsS.
Qed.

Lemma counter_call_incr_and_get (i:nat) f :
  IsCounterIncrAndGet i f -∗
  wps (Some ∅) (call_clo f []) (fun n => ⌜n=(1+i)%nat⌝ ∗ IsCounterIncrAndGet (1+i) f).
Proof.
  iIntros "[%r (? & ? & ?)]".
  wps_call_spec as "Hspec".
  unfold incr_and_get_clo_spec.
  wps_context r.
  iSpecialize ("Hspec" with "[$]").
  iApply (@wps_mono with "[$]").
  iIntros (?) "(? & ? & Hclo)".
  iFrame. iIntros. iExists _. iFrame.
Qed.

Lemma counter_both_free i f :
  Stackable f 1%Qp ∗ f ↤ ∅ ∗ IsCounterIncrAndGet i f =#=∗
  ♢3.
Proof.
  iIntros "(? & ? & [%ref (Href & Href2 & ?)])".
  iIntros (? ? ?) "Hi".
  iMod (spec_esupd_free f with "[$] [$]") as "(Hi & Hc & Hg)".
  iDestruct "Hg" as "(? & _)". simpl.
  iMod (free_ref ref with "[$] [$]") as "(? & ? & _)".
  iDestruct (diamonds_join with "[$]") as "?".
  rew_qz.
  by iFrame.
Qed.
End CounterIncrAndGet.
