From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.language Require Import notation.

From spacelambda Require Import more_space_lang wp_all wpc triple.

From spacelambda.examples.tactics Require Import tactics.
From spacelambda.examples.list Require Import list.

(* This file introduces possibly bounded stacks and their specifications. *)

Definition size_lt n (c:option positive) :=
  match c with
  | Some c => n < Pos.to_nat c
  | None => True end.

Module Type StackOf.
  Parameter capacity : option positive.

  Parameter stack_empty : val.
  Parameter stack_push  : val.
  Parameter stack_pop   : val.
  Parameter stack_is_empty : val.
  Parameter stack_is_full  : val.

  Axiom locs_stack_empty : locs stack_empty = ∅.
  Axiom locs_stack_push  : locs stack_push  = ∅.
  Axiom locs_stack_pop   : locs stack_pop   = ∅.
  Axiom locs_stack_is_empty : locs stack_is_empty = ∅.
  Axiom locs_stack_is_full : locs stack_is_full = ∅.

  Parameter StackOf : forall `{interpGS Σ} {A} (R:A -> val -> iProp Σ),
      list (A * (Qz * Qp)) -> loc -> iProp Σ.

  Parameter empty_cost : Qz.
  Parameter cell_cost : Qz.

  Axiom stack_empty_spec : forall `{interpGS Σ} A (R:A -> val -> iProp Σ),
      CODE (stack_empty [[]])
      PRE  (♢ empty_cost)
      POST (fun s => StackOf R [] s ∗ Stackable s 1%Qp ∗ s ↤ ∅).

  Axiom stack_push_spec : forall `{interpGS Σ} A (R:A -> val -> iProp Σ),
    forall s qp qz v x xs,
      size_lt (length xs) capacity ->
      qz ≠ 0%Qz ->
      CODE (stack_push [[v, s]])
      SOUV {[s]}
      PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅)
      POST (fun (_:unit) => StackOf R ((x,(qz,qp))::xs) s).

  Axiom stack_pop_spec : forall `{interpGS Σ} A (R:A -> val -> iProp Σ),
    forall s qp qz x xs,
      CODE (stack_pop [[s]])
      SOUV {[s]}
      PRE  (StackOf R ((x,(qz,qp))::xs) s)
      POST (fun v => R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).

  Axiom stack_is_empty_spec : forall `{interpGS Σ} A (R:A -> val -> iProp Σ),
    forall xs s,
      CODE (stack_is_empty [[s]])
      SOUV {[s]}
      PRE  (StackOf R xs s)
      POST (fun b => ⌜b=bool_decide (xs=nil)⌝ ∗ StackOf R xs s).

  Axiom stack_is_full_spec : forall `{interpGS Σ} A (R:A -> val -> iProp Σ),
    forall xs s,
      CODE (stack_is_full [[s]])
      SOUV {[s]}
      PRE (StackOf R xs s)
      POST (fun (b:bool) => ⌜ b <-> (¬ (size_lt (length xs) capacity))⌝ ∗ StackOf R xs s).

  Axiom stack_free : forall `{interpGS Σ} A (R:A -> val -> iProp Σ),
    forall s xs,
      Stackable s 1%Qp ∗ s ↤ ∅ ∗ StackOf R xs s =#=∗
      ♢(empty_cost + cell_cost*length xs) ∗ † s ∗
      (∃ vs, soup R ∅ xs vs).
End StackOf.

Module Type Capacity.
  Parameter capacity : positive.
End Capacity.

Module MoreStackOf(St:StackOf).
Export St.

Lemma stack_pop_spec' `{interpGS Σ} A (R:A -> val -> iProp Σ) xs s:
  xs ≠ nil ->
  CODE (stack_pop [[s]])
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun v => ∃ x xs' qz qp, ⌜xs=(x,(qz,qp))::xs'⌝ ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅ ∗ StackOf R xs' s ∗ ♢ cell_cost).
Proof.
  iIntros. destruct xs as [|(x,(qz,qp)) xs']; try easy.
  wps_mono "[-]".
  { iApply stack_pop_spec. iFrame. }
  iIntros (?) "(? & ? & ? & ? & ?)".
  iExists _,_,_,_. iFrame. eauto.
Qed.

(* A stack free for empty stacks *)
Lemma empty_stack_free `{interpGS Σ} A (R:A -> val -> iProp Σ) s :
  Stackable s (1)%Qp ∗ s ↤ ∅ ∗ StackOf R nil s =#=∗
    ♢ empty_cost.
Proof.
  iIntros "(? & ?)". iIntros.
  iMod (stack_free with "[$] [$]") as "(? & ? & ?)".
  iFrame.
  simpl. rewrite right_absorb right_id.
  by iFrame.
Qed.

(* LATER stack_free which frees the content of its children. *)
End MoreStackOf.

Module StackDominant(St:StackOf).
Export St.

Definition StackDominantOf `{!interpGS Σ} {A} (R:A -> val -> iProp Σ)
  qp (xs:list A) (s:loc) : iProp Σ :=
  StackOf R (fmap (fun v => (v,(1%Qz,qp))) xs) s.

Lemma stack_is_empty_spec_dominant `{interpGS Σ} A (R:A -> val -> iProp Σ) qp xs s :
  CODE (stack_is_empty [[s]])
  SOUV {[s]}
  PRE  (StackDominantOf R qp xs s)
  POST (fun b => ⌜b=bool_decide (xs=nil)⌝ ∗ StackDominantOf R qp xs s).
Proof.
  iIntros.
  wps_apply @stack_is_empty_spec as (?) "(%E & ?)".
  iFrame. iPureIntro. rewrite E.
  now destruct xs.
Qed.

Lemma stack_is_full_spec_dominant `{interpGS Σ} A (R:A -> val -> iProp Σ) qp xs s :
  CODE (stack_is_full [[s]])
  SOUV {[s]}
  PRE  (StackDominantOf R qp xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackDominantOf R qp xs s).
Proof.
  iIntros.
  wps_apply @stack_is_full_spec as (?) "(? & ?)".
  rewrite fmap_length. eauto.
Qed.

Lemma stack_empty_dominant_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) qp :
  CODE (stack_empty [[]])
  PRE (♢ empty_cost)
  POST (fun s => StackDominantOf R qp [] s ∗ Stackable s (1)%Qp ∗ s ↤ ∅).
Proof.
  iIntros.
  wps_apply @stack_empty_spec.
  iFrame.
Qed.

Lemma stack_push_dominant_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) qp x v xs s :
  size_lt (length xs) capacity ->
  CODE (stack_push [[v, s]])
  SOUV {[s]}
  PRE (♢ cell_cost ∗ StackDominantOf R qp xs s ∗ v ↤? ∅ ∗ vStackable v qp ∗ R x v)
  POST (fun (_:unit) => StackDominantOf R qp (x::xs) s).
Proof.
  iIntros (?) "(? & ? & ? & ? & ?)".
  wps_apply @stack_push_spec.
  { rewrite fmap_length. easy. }
  { easy. }
  iFrame.
Qed.

Lemma stack_pop_dominant_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) qp x xs s :
  CODE (stack_pop [[s]])
  SOUV {[s]}
  PRE (StackDominantOf R qp (x::xs) s)
  POST (fun v => R x v ∗ v ↤? ∅ ∗ vStackable v qp ∗ StackDominantOf R qp xs s ∗ ♢ cell_cost).
Proof.
  iIntros.
  wps_apply @stack_pop_spec as "(? & ? & ? & ?)".
  iFrame.
Qed.

Lemma stack_pop_dominant_spec' `{!interpGS Σ} A (R:A -> val -> iProp Σ) qp xs s :
  xs ≠ nil ->
  CODE (stack_pop [[s]])
  SOUV {[s]}
  PRE (StackDominantOf R qp xs s)
  POST (fun v => ∃ y ys, ⌜xs=y::ys⌝ ∗ R y v ∗ v ↤? ∅ ∗ vStackable v qp ∗ StackDominantOf R qp ys s ∗ ♢ cell_cost).
Proof.
  iIntros (?) "?".
  destruct xs as [|v tl]; try easy.
  wps_apply @stack_pop_dominant_spec as "(? & ? & ? & ? & ?)".
  iExists _,_.
  iFrame. easy.
Qed.

Lemma stack_dominant_free `{!interpGS Σ} A (R:A -> val -> iProp Σ) qp (xs:list A) s :
  Stackable s (1)%Qp ∗ s ↤ ∅ ∗ StackDominantOf R qp xs s =#=∗
  ♢(empty_cost+cell_cost*length xs) ∗ †s ∗
  (∃ vs, [∗ list] x;v ∈ xs; vs,
     v ↤? ∅ ∗ vStackable v qp ∗ R x v).
Proof.
  iIntros "(Hk & Hs1 & Hs2)". iIntros.
  iMod (stack_free _ R s (((λ v, (v, (1%Qz,qp))) <$> xs)) with "[$] [$]") as "(? & ? & ? & [%vs Hvs])".
  iModIntro. iFrame. rewrite fmap_length. iFrame.
  iExists vs.

  iInduction xs as [] "IH" forall (vs); simpl.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%E". subst. simpl. easy. }
  { iDestruct( big_sepL2_cons_inv_l with "[$]") as "[%v' [%vs' [%E ((? & ? & ?) & Hvs)]]]".
    subst. simpl. iFrame. iApply "IH". iFrame. }
Qed.
End StackDominant.

(* In the paper, we show a restricted interface.
   We show here that StackOf refines to it. *)
Module PaperStack(S:StackOf).
Import S.

Definition Stack `{interpGS Σ} (L:list (val * Qp)) (l:loc) : iProp Σ :=
  @StackOf _ _ val (fun (x y:val) => ⌜x = y⌝)%I (dupf <$> L) l.

Lemma stack_empty_spec `{interpGS Σ} :
    CODE (stack_empty [[]])
    PRE  (♢ empty_cost)
    POST (fun s => Stack [] s ∗ s ↩ ∅).
Proof.
  iIntros.
  wps_apply stack_empty_spec.
  rewrite handle_one. iStepsS.
Qed.

Lemma stack_push_spec `{interpGS Σ} s qp x xs :
  size_lt (length xs) capacity ->
  CODE (stack_push [[x, s]])
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ Stack xs s ∗ x ↩{qp} ∅)
  POST (fun (_:unit) => Stack ((x,qp)::xs) s).
Proof.
  iIntros (?) "(? & ? & ? & ?)".
  wps_apply stack_push_spec; eauto.
  { rewrite fmap_length //. }
  { apply Qp_to_Qz_ne_zero. }
Qed.

Lemma stack_pop_spec `{interpGS Σ} s qp x xs :
  CODE (stack_pop [[s]])
  SOUV {[s]}
  PRE  (Stack ((x,qp)::xs) s)
  POST (fun v => v ↩{qp} ∅ ∗ Stack xs s ∗ ♢ cell_cost).
Proof.
  iIntros.
  wps_apply stack_pop_spec as "(% & ? & ? & ?)".
  subst. iFrame.
Qed.

Lemma stack_is_empty_spec `{interpGS Σ} xs s :
  CODE (stack_is_empty [[s]])
  SOUV {[s]}
  PRE  (Stack xs s)
  POST (fun b => ⌜b=bool_decide (xs=nil)⌝ ∗ Stack xs s).
Proof.
  iIntros.
  wps_apply stack_is_empty_spec as "(% & ?)".
  iFrame.
  iPureIntro. destruct xs; simpl in *; naive_solver.
Qed.

Lemma stack_is_full_spec `{interpGS Σ} xs s :
  CODE (stack_is_full [[s]])
  SOUV {[s]}
  PRE (Stack xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ Stack xs s).
Proof.
  iIntros.
  wps_apply stack_is_full_spec as "(%E & ?)".
  iFrame. iPureIntro. rewrite fmap_length in E.
  eauto.
Qed.

Lemma stack_free `{interpGS Σ} (xs:list (val*Qp)) (s:loc) :
  s ↩ ∅ ∗ Stack xs s =[true|∅]=∗
    ♢(empty_cost + cell_cost*length xs) ∗ † s ∗
    ([∗ list] x ∈ xs, (fst x) ↩{snd x} ∅).
Proof.
  rewrite handle_one.
  iIntros "((?&?)&?)". iIntros.
  iMod (stack_free with "[$] [$]") as "(? & ? & ? & [%vs ?])".
  rewrite fmap_length. iFrame. iModIntro.
  iApply soup_mixer. iFrame.
Qed.
End PaperStack.
