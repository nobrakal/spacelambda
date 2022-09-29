From iris.bi.lib Require Import fractional.

From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap binders gmultiset.

From spacelambda.fracz Require Export qz smultiset.
From spacelambda.language Require Import language.

From spacelambda Require Import more_space_lang wp interp.

Section Utils.
Context `{interpGS Σ}.

Definition vStackable `{!interpGS Σ} v q :=
  match v with
  | val_loc l => Stackable l q
  | _ => True%I end.

Global Instance mapsto_fractional v : Fractional (λ q, vStackable v q)%I.
Proof.
  destruct v; simpl; iIntros (? ?); try (iSplit; easy).
  iSplit. iIntros "(? & ?)". iFrame. iIntros "(Hp & Hq)".
  iApply (Stackable_join with "[Hp]"); iFrame.
Qed.

Global Instance mapsto_as_fractional q v :
  AsFractional (vStackable v q) (λ q, vStackable v q)%I q.
Proof. constructor; eauto. apply _. Qed.

Lemma vStackable_confront `{!interpGS Σ} v1 v2 p :
  vStackable v1 p ∗ vStackable v2 1%Qp -∗ ⌜diff_loc v1 v2⌝.
Proof.
  iIntros "(? & ?)".
  destruct v1; try (simpl; iFrame; iPureIntro; easy).
  destruct v2; try (simpl; iFrame; iPureIntro; easy).
  simpl. iApply Stackable_confront. iFrame.
Qed.

Definition group_pointedbys (E:smultiset loc) (vs:list val) (lq:list Qz) : iProp Σ :=
  [∗ list] v;q ∈ vs;lq, v ↤?{q} E.

Lemma group_pointedbys_pred_dealloc b R l vs lq :
  † l ∗ group_pointedbys {[+ l +]} vs lq =[b|R]=∗ group_pointedbys ∅ vs lq.
Proof.
  iRevert (lq).
  iInduction vs as [|] "IH"; iIntros (lq) "(? & ?)".
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hl". subst.
    iIntros. iModIntro. iFrame. easy. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%x [%xs (%He & ? & ?)]]". subst.
    iIntros.
    iMod (vmapsfrom_cleanup with "[$] [$]") as "(? & ? & ?)".
    iMod ("IH" with "[$] [$]") as "(? & ?)".
    iFrame.
    assert ({[+ l +]} ⊎ {[-l-]} ≡ ∅) as -> by smultiset_solver.
    by iFrame. }
Qed.

Definition group_notctxs (vs:list val) (lq:list Qp) : iProp Σ :=
  [∗ list] v;q ∈ vs;lq, vStackable v q.

(* A group of Stackables is similar to Stackables with filtered locations. *)
Lemma group_borrow_Stackables vs lq :
  group_notctxs vs lq ==∗ ∃ M, Stackables M ∗ ⌜dom M = locs vs⌝ ∗ (Stackables M -∗ group_notctxs vs lq).
Proof.
  iStartProof.
  iRevert (lq).
  iInduction vs as [|v] "IH".
  { iIntros. iMod Stackables_empty. iExists ∅ . iFrame.
    rewrite dom_empty_L. auto_locs. eauto. }
  iIntros (ls) "H".
  iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%qp [%tl (%Hl & ? & ?)]]".
  subst.
  iMod ("IH" with "[$]") as "[%M (? & %Hdm & Hk)]". iClear "IH". iModIntro.
  destruct (decide (is_loc v)).
  { destruct v as [l| | |]; try easy.
    simpl. iDestruct (Stackables_union with "[$]") as "?". iExists _.
    iFrame.
    iSplitR.
    { iPureIntro. rewrite dom_op. auto_locs. rewrite dom_singleton_L. set_solver. }
    iIntros.
    iDestruct (Stackables_split with "[$]") as "[? ?]".
    unfold group_notctxs. simpl. iFrame. iApply "Hk". iFrame. }
  { iExists _. iFrame. iSplitR.
    { iPureIntro. auto_locs. rewrite locs_no_loc //. set_solver. }
    { iIntros. iApply "Hk". iFrame. } }
Qed.

End Utils.
