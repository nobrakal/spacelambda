From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz qz_cmra smultiset_cmra.
From spacelambda.language Require Import notation.
From spacelambda Require Import interp.

From spacelambda Require Import more_space_lang wp_all wpc triple.

From spacelambda.examples.tactics Require Import tactics.
From spacelambda.examples.lib Require Import utils.
From spacelambda.examples.list Require Import list.

(* ------------------------------------------------------------------------ *)
(* rev_append with its two specifications. *)

Definition list_rev_append : val :=
  μ: "self", [["xs", "ys"]],
    let: "b" := list_is_nil [["xs"]] in
    if: "b" then "ys" else
    let: "hd" := list_head [["xs"]] in
    let: "tl" := list_tail [["xs"]] in
    let: "nys" := list_cons [["hd", "ys"]] in
    "self" [["tl", "nys"]].

Definition list_rev : val :=
  λ: [["xs"]],
    let: "n" := list_nil [[]] in
    list_rev_append [["xs", "n"]].

Section RevDestructive.
Import ListsOf.
Context `{interpGS Σ}.

(* We can express List.rev with ListOf only in the destructive case. *)
Lemma list_rev_append_spec {A} (R:A -> val -> iProp Σ) Lxs xs Lys ys :
  CODE (list_rev_append [[xs,ys]])
  PRE (ListOf R Lxs xs ∗ Stackable xs 1%Qp ∗ xs ↤ ∅ ∗
       ListOf R Lys ys ∗ Stackable ys 1%Qp ∗ ys ↤ ∅)
  POST (fun (zs:loc) => ListOf R (rev Lxs ++ Lys) zs ∗ Stackable zs 1%Qp ∗ zs ↤ ∅ ∗ ♢1 ).
Proof.
  iStartProof.
  iRevert (xs ys Lys).
  iInduction Lxs as [|(x,(q,p)) Lxs] "IH"; iIntros (xs ys Lys) "(Hxs1 & Hxs2 & Hxs3 & Hys1 & Hys2 & Hys3)".
  all: wps_call; wps_bind; wps_apply list_is_nil_spec as (b) "(%Hb & Hxs1)"; iIntros "(? & ?)".
  { wps_if. rewrite Hb.
    wps_context ys.
    iApply @wps_esupd.
    { set_solver. }
    { apply list_free. }
    iFrame.
    simpl.
    iIntros "(? & _ & _)".
    wps_val. iIntros.
    iFrame. conclude_diamonds. }
  wps_if. rewrite Hb. simpl.
  wps_bind.
  wps_apply list_head_spec as (hd) "(? & Hmhd & ? & ?)".
  iIntros "(? & ?)".
  wps_bind.
  wps_apply list_tail_spec as (tl) "(? & ? & ? & ?)".
  iIntros "? ?".

  iDestruct (Stackable_confront xs tl with "[$]") as "%H1".
  iDestruct (Stackable_confront xs ys with "[$]") as "%H2".
  iDestruct (vStackable_confront hd xs with "[$]") as "%H3".

  iDestruct (vmapsfrom_correct with "[$]") as "%Hq".

  wps_free xs.
  { auto_locs. destruct hd; set_solver. }

  clear H1 H2 H3.

  iApply (wps_cleanup_vsingleton _ hd with "[$]"). iIntros "(? & ?)".
  iApply (wps_cleanup_vsingleton  _ tl with "[$]"). iIntros "(? & _)".
  simpl. assert (({[+ xs +]} ⊎ {[-xs-]}) ≡ ∅) as -> by smultiset_solver.

  wps_bind.

  wps_apply list_cons_spec as (nys) "(? & ? & ?)".
  { intros. destruct Hq; eauto. smultiset_solver. }
  clear Hq.
  iIntros.
  wps_apply "IH".
  rewrite -app_assoc cons_middle. simpl. iFrame.
Qed.

Lemma list_rev_spec {A} (R:A -> val -> iProp Σ) Lxs xs :
  CODE (list_rev [[xs]])
  PRE (♢ 1 ∗ ListOf R Lxs xs ∗ Stackable xs 1%Qp ∗ xs ↤ ∅)
  POST (fun (zs:loc) => ListOf R (rev Lxs) zs ∗ Stackable zs 1%Qp ∗ zs ↤ ∅ ∗ ♢1 ).
Proof.
  iIntros "(? & ? & ? & ?)".
  wps_call.
  wps_bind.
  wps_apply list_nil_spec. iIntros.
  wps_apply @list_rev_append_spec.
  rewrite right_id_L.
  iFrame.
Qed.

Import Lists.

Lemma list_rev_append_spec_ Lxs xs Lys ys :
  CODE (list_rev_append [[xs,ys]])
  PRE (List Lxs xs ∗ Stackable xs 1%Qp ∗ xs ↤ ∅ ∗
       List Lys ys ∗ Stackable ys 1%Qp ∗ ys ↤ ∅)
  POST (fun (zs:loc) => List (rev Lxs ++ Lys) zs ∗ Stackable zs 1%Qp ∗ zs ↤ ∅ ∗ ♢1 ).
Proof. apply list_rev_append_spec. Qed.

(* Then List.rev for List is a direct consequence. *)
Lemma list_rev_spec_  Lxs xs :
  CODE (list_rev [[xs]])
  PRE (♢ 1 ∗ List Lxs xs ∗ Stackable xs 1%Qp ∗ xs ↤ ∅)
  POST (fun (ys:loc) => List (rev Lxs) ys ∗ Stackable ys 1%Qp ∗ ys ↤ ∅ ∗ ♢1 ).
Proof. apply list_rev_spec. Qed.
End RevDestructive.

Section RevPreserving.
Import Lists.
Context `{interpGS Σ}.

Definition halves {A} (lst: list (A * (Qz * Qp))) :=
  (fun '(x,(q,p)) => (x,((q/2)%Qz,(p/2)%Qp))) <$> lst.

Lemma list_rev_append_spec'  Lxs xs Lys ys :
  CODE (list_rev_append [[xs,ys]])
  SOUV {[xs]}
  PRE (♢ (3 * length Lxs) ∗ List Lxs xs ∗
       List Lys ys ∗ Stackable ys 1%Qp ∗ ys ↤ ∅)
  POST (fun (zs:loc) => List (rev (halves Lxs) ++ Lys) zs ∗ Stackable zs 1%Qp ∗ zs ↤ ∅ ∗ List (halves Lxs) xs).
Proof.
  iStartProof.
  iRevert (xs ys Lys).
  iInduction Lxs as [|(x,(q,p)) Lxs] "IH"; iIntros (xs ys Lys) "(Hdiams & Hxs & Hys1 & Hys2 & Hys3)".
  all: wps_call; wps_bind; wps_apply list_is_nil_spec as (b) "(%Hb & Hxs)"; iIntros;
    wps_if; rewrite Hb.
  { wps_val. iFrame. }
  wps_bind.
  wps_apply list_head_spec as (hd) "(%Hx & Hmhd & Hchd & ?)". subst.
  iIntros.
  wps_bind.
  wps_apply list_tail_spec as (tl) "(? & ? & ? & ?)".
  iIntros "? (? & ?)".

  iDestruct (vmapsfrom_correct with "[$]") as "%Hq".

  wps_bind.

  assert (is_loc hd -> q/2 ≠ 0)%Qz as Hdq.
  { intros ? E. apply Qz_div_eq_zero in E. destruct Hq as [|Hq]; eauto.
    apply Hq in E.
    smultiset_solver. }

  rewrite <- (Qz_div_2 q).
  assert ( {[+ xs +]} ≡  {[+ xs +]} ⊎ ∅) as -> by smultiset_solver.
  iDestruct (vmapsfrom_split with "[$]") as "(? & ?)".
  1,2:intros E; apply Hdq in E; intros; congruence.

  mine 3.
  wps_apply list_cons_spec as (nys) "(? & ? & ?)".
  { eauto. }
  iIntros.

  wps_context tl.
  iApply (@wps_weak _ _ loc _ {[tl]}).
  { set_solver. }
  wps_apply "IH".

  iSplitL "Hdiams". conclude_diamonds.
  iIntros (?) "(? & ? & ? & ?) ?". iFrame.
  rewrite right_id.
  rewrite -app_assoc cons_middle. iFrame.
  rewrite Qz_div_2. iFrame.

  simpl. iFrame. iApply List_cons. iStepsS.
Qed.

Lemma list_rev_spec' Lxs xs :
  CODE (list_rev [[xs]])
  SOUV {[xs]}
  PRE (♢ (3*length Lxs + 1) ∗ List Lxs xs)
  POST (fun (ys:loc) => List (rev (halves Lxs)) ys ∗ Stackable ys 1%Qp ∗ ys ↤ ∅ ∗ List (halves Lxs) xs).
Proof.
  iIntros "(? & ?)".
  wps_call.
  wps_bind. mine 1.
  wps_apply list_nil_spec. iIntros.
  wps_apply @list_rev_append_spec'.
  iSplitL. conclude_diamonds.
  rewrite right_id_L.
  eauto.
Qed.

End RevPreserving.

Section PaperRevAppend.

Import Lists.
Context `{interpGS Σ}.

Lemma list_rev_append_destructive_spec Lxs xs Lys ys :
  CODE (list_rev_append [[xs,ys]])
  PRE (List Lxs xs ∗ xs ↩ ∅ ∗
       List Lys ys ∗ ys ↩ ∅)
  POST (fun (zs:loc) => List (rev Lxs ++ Lys) zs ∗ zs ↩ ∅ ∗ ♢1 ).
Proof.
  rewrite !handle_one. simpl.
  iIntros "(?&(?&?)&?&(?&?))".
  wps_apply list_rev_append_spec_.
  rewrite !handle_one. iStepsS.
Qed.

Lemma list_rev_append_preserving_spec Lxs xs Lys ys :
  CODE (list_rev_append [[xs,ys]])
  SOUV {[xs]}
  PRE (♢ (3 * length Lxs) ∗ List Lxs xs ∗
       List Lys ys ∗ ys ↩ ∅)
  POST (fun (zs:loc) => List (rev (halves Lxs) ++ Lys) zs ∗ zs ↩ ∅ ∗ List (halves Lxs) xs).
Proof.
  rewrite !handle_one. simpl.
  iIntros "(?&?&?&(?&?))".
  wps_apply list_rev_append_spec'.
  rewrite !handle_one. iStepsS.
Qed.
End PaperRevAppend.
