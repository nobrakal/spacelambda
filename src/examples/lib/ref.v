From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.language Require Import notation.
From spacelambda Require Import interp triple.

From spacelambda Require Import more_space_lang wp_all.

From spacelambda.examples.tactics Require Import tactics.

Definition ref : val :=
  λ: [["v"]],
    let: "x" := alloc 1 in
    "x".[0] <- "v";;
    "x".

Definition get : val :=
  λ: [["l"]],
    "l".[0].

Definition set : val :=
  λ: [["l", "v"]],
    "l".[0] <- "v".

Definition incr : val :=
  λ: [["r"]] ,
    let: "i" := get [["r"]] in
    let: "j" := 1 '+ "i" in
    set [["r","j"]].

Section Ref_spec.

Context `{!interpGS Σ}.

Definition isRef (v:val) (l:loc) := (l ↦ BBlock [v])%I.

Lemma ref_spec q r (v:val) :
  q ≠ 0%Qz ->
  CODEFF (ref [[v]])
  PRE  (♢ 1 ∗ v ↤?{q} r)
  POST (fun l => isRef v l ∗ v ↤?{q} (r ⊎ {[+l+]}) ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  repeat (iStepsS; iApply wp_enc_let_nofree).
Qed.

Lemma ref_spec_no_loc (v:val) :
  is_loc v = false ->
  CODEFF (ref [[v]])
  PRE  (♢ 1)
  POST (fun l => isRef v l ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  iIntros.
  replace ∅ with (locs v) by (destruct v; set_solver).
  wps_apply (ref_spec 1 ∅ v); eauto.
  iSplitL. destruct v; try easy.
  iStepsS.
Qed.

Lemma get_spec l v :
  CODEFF (get [[l]])
  PRE (isRef v l)
  POST (fun w => ⌜v=w⌝ ∗ isRef v l).
Proof.
  iStepsS.
Qed.

(* LATER is there a better mono lemma for this proof ? *)
Lemma get_spec_enc `{Enc A} l (v:A) :
  CODEFF (get [[l]])
  PRE (isRef (enc v) l)
  POST (fun w => ⌜w=v⌝ ∗ isRef (enc v) l).
Proof.
  iIntros.
  iDestruct (get_spec with "[$]") as "?".
  iApply wps_end_val.
  iApply (wps_mono with "[$]").
  iIntros (?) "(%Hv & ?)". subst.
  iStepsS.
Qed.

Lemma set_spec l v w qw r :
  qw ≠ 0%Qz ->
  CODEFF (set [[l, w]])
  PRE  (isRef v l ∗ w↤?{qw} r)
  POST (fun tt => isRef w l ∗ w ↤?{qw} (r ⊎ {[+ l +]}) ∗ v ↤?{0%Qz} {[-l-]}).
Proof.
  iStepsS.
Qed.

Lemma set_spec_no_loc l v (w:val):
  is_loc w = false ->
  CODEFF (set [[l, w]])
  PRE  (isRef v l)
  POST (fun (_:unit) => isRef w l).
Proof.
  iStepsS.
Qed.

Lemma free_ref l v :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ isRef v l =#=∗ ♢ 1 ∗ †l.
Proof.
  iIntros "(? & ? & ?)". iIntros. unfold isRef.
  iMod (logical_free with "[$] [$]") as "(? & ? & ?)"; try easy.
  simpl.  now iFrame.
Qed.

Lemma incr_spec (r:loc) (i:nat) :
  isRef i r -∗
  wps (Some ∅) (incr [[r]])%T (fun (_:unit) => isRef (1+i) r).
Proof.
  iIntros.
  wps_call.
  wps_nofree.
  wps_bind.
  wps_apply get_spec as "(%Hv & ?)". subst. simpl.
  wps_bin_op.
  wps_apply (set_spec_no_loc r).
  all:easy.
Qed.

End Ref_spec.
