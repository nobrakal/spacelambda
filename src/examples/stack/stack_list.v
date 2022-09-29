From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.language Require Import notation.
From spacelambda Require Import interp triple.

From spacelambda Require Import more_space_lang wp_all wpc triple.
From spacelambda.examples Require Import tactics ref list stack.

Import ListsOf.

(* We encode stacks as pointers to a linked list. *)

Module StackList : StackOf with
Definition capacity := @None positive.
Definition capacity := @None positive.

Definition stack_empty : val :=
  λ: [[]],
    let: "l" := list_nil [[]] in
    ref [["l"]].

Definition stack_push : val :=
  λ: [["v", "s"]],
    let: "l" := get [["s"]] in
    let: "l2" := list_cons [["v","l"]] in (* here l is still pointed by s. *)
    set [["s", "l2"]].

Definition stack_pop : val :=
  λ: [["s"]],
    let: "l" := get [["s"]] in
    let: "x" := list_head [["l"]] in
    let: "l2" := list_tail [["l"]] in
    set [["s","l2"]];;
    "x".

Definition stack_is_empty : val :=
  λ: [["s"]],
    let: "l" := get [["s"]] in
    list_is_nil [["l"]].

Definition stack_is_full : val :=
  λ: [["_"]], 0.

Lemma locs_stack_empty : locs stack_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_push : locs stack_push = ∅.
Proof. easy. Qed.
Lemma locs_stack_pop : locs stack_pop = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_empty : locs stack_is_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_full : locs stack_is_full = ∅.
Proof. easy. Qed.

(* Constant factors *)
Definition empty_cost : Qz := 2.
Definition cell_cost  : Qz := 3.

(* Stack has the full ownership of the pointer _and_ of the list.
   It even possesses a part of its Stackable, as the user will not deallocate the
   stack without giving "Stack" *)
Definition StackOf `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qz * Qp))) (s:loc) : iProp Σ :=
  ∃ l:loc,
    (* s is a reference to l *)
    isRef l s ∗
    (* The reference is invisible from the outside *)
    Stackable l 1%Qp ∗ l ↤ {[+ s +]} ∗
    (* l denotes a list with content xs *)
    ListOf R xs l.

Ltac destruct_stack Hs :=
  iDestruct Hs as "[%l (Hs & ? & ? & Hl)]".

Lemma stack_is_empty_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun n => ⌜n ≠ 0 <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  wps_call.
  wps_bind.
  wps_nofree.
  wps_apply get_spec as "[%E Hs]"; subst.
  wps_apply @list_is_nil_spec as "(%Hp & ?)".
  iStepsS.
Qed.

Lemma stack_is_full_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun n => ⌜n ≠ 0 <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof. iStepsS. Qed.

Lemma stack_empty_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ Stackable s (1)%Qp ∗ s ↤ ∅).
Proof.
  iIntros.
  wps_call.
  wps_bind. unfold empty_cost.
  assert (2%Qz=1%Qz+1)%Qz as -> by compute_done.
  iDestruct (diamonds_split with "[$]") as "[? ?]".
  wps_apply @list_nil_spec as (l) "(? & ? & Hfl)" by set_solver'.

  wps_context l.
  assert ({[l]} = locs (#l)%V) as -> by (now auto_locs).
  wps_nofree.
  wps_apply @ref_spec as "(? & ? & ? & ? ) ?". easy.
  rewrite left_id. iFrame.
  iExists _. iFrame.
Qed.

Lemma stack_push_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) s qp qz v x xs :
  size_lt (length xs) capacity ->
  qz ≠ 0%Qz ->
  CODE (stack_push [[v, s]])
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅)
  POST (fun tt => StackOf R ((x,(qz,qp))::xs) s).
Proof.
  iIntros (_ ?) "(? & Hs & ? & ? & ?)".
  destruct_stack "Hs".
  wps_call.
  wps_bind.
  wps_nofree.
  wps_apply @get_spec as "[%E Hs]". subst.
  iIntros.
  wps_bind.
  wps_context v.
  wps_apply @list_cons_spec_debt as (l') "(Hcl' & Hfl' & Hl')". easy.
  iIntros. iSpecialize ("Hl'" with "[$]").
  rewrite opposite_singleton.
  wps_nofree.
  wps_apply set_spec as "(? & ? & ?) ?". easy.
  iIntros (_) "(? & ? & ?)".
  iExists _. rewrite left_id. iFrame.
  iApply "Hl'". iFrame.
Qed.

Lemma stack_pop_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) s qp qz x xs :
  CODE (stack_pop [[s]])
  SOUV {[s]}
  PRE  (StackOf R ((x,(qz,qp))::xs) s)
  POST (fun v => R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  wps_call.
  wps_bind.

  wps_nofree.
  wps_apply @get_spec as "[%E Hs]". subst.
  wps_bind.

  wps_apply @list_head_spec as "(? & ? & ? & Hl) ?". subst.

  wps_context v.
  wps_bind.

  wps_apply @list_tail_spec as "(? & ? & Hftl & ?)".
  wps_bind.

  wps_nofree.
  wps_apply set_spec as  "(? & ? & ?)". easy.

  iDestruct (mapsfrom_join l with "[$] [$]") as "?".
  assert ( ({[-s-]} ⊎ {[+ s +]}) ≡ ∅) as -> by smultiset_solver.
  rewrite left_id_L.

  (* We want now to free l, and thus have prove that l ∉ locs v *)
  iApply (wps_confront_Stackable l with "[$]"). iIntros "%Hl ?".

  wps_free l. simpl.

  (* Now we clean. *)
  iApply (wps_cleanup_vsingleton l with "[$]").
  iIntros "[? ?]".
  iApply (wps_cleanup_singleton l with "[$]").
  iIntros "[? ?]".

  (* Some rewriting *)
  assert (({[+ l +]} ⊎ {[-l-]}) ≡ ∅) as -> by smultiset_solver.
  assert (({[+ l; s +]} ⊎ {[-l-]}) ≡ {[+s+]}) as -> by smultiset_solver.

  (* Conclude. *)
  iStepsS.
Qed.

Lemma stack_free `{!interpGS Σ} A (R:A -> val -> iProp Σ) s xs :
  Stackable s 1%Qp ∗ s ↤ ∅ ∗ StackOf R xs s =#=∗
  ♢(empty_cost + cell_cost*length xs) ∗ †s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(Hs1 & Hs2 & Hs)". iIntros (? ? ?) "Hi".
  destruct_stack "Hs".

  iMod (free_ref s l with "[$] [$]") as "(Hi & ? & #Hds)".
  iMod (mapsfrom_cleanup with "[$] [Hi]") as "(? & ?)"; first iFrame.
  rewrite disj_union_sinlgeton_opposite.

  iMod (list_free _ R l with "[$] [$]") as "(? & ? & ? & ?)".
  iDestruct (diamonds_join with "[$]") as "?".
  iFrame. iModIntro. iFrame "Hds".
  iApply (diamonds_eq with "[$]").
  rewrite /empty_cost /cell_cost. rew_qz. lia.
Qed.
End StackList.
