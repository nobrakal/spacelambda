From iris.proofmode Require Export proofmode.

From glaneur.fracz Require Import qz smultiset.
From glaneur.language Require Import language.
From glaneur.spacelang Require Import predecessors.

From glaneur Require Import ph interp.

(* ------------------------------------------------------------------------ *)

(* The predicate [vmapsfrom] takes a value [v] as its first argument,
   whereas [mapsfrom] takes a location [l']. *)

Definition vmapsfrom `{!interpGS Σ} v q ls : iProp Σ :=
  match v with
  | val_loc l' =>
      l' ↤{q} ls
  | _ =>
      True
  end.

Global Instance vmapsfrom_proper `{!interpGS Σ} v q : Proper ((≡) ==> (≡)) (vmapsfrom v q).
Proof.
  intros ? ? E.
  destruct v; try easy.
  rewrite E //.
Qed.

Notation "v ↤?{ q } ls" :=
  (vmapsfrom v%Qz q ls)
  (at level 20, format "v  ↤?{ q }  ls")
: bi_scope.

Notation "v ↤? ls" :=
  (vmapsfrom v 1%Qz ls)
  (at level 20, format "v  ↤?  ls")
: bi_scope.

Lemma vmapsfrom_join `{!interpGS Σ} v q1 q2 ls1 ls2 :
  v ↤?{q1} ls1 ∗ v ↤?{q2} ls2 -∗ v ↤?{q1+q2} (ls1 ⊎ ls2) .
Proof.
  destruct v; simpl vmapsfrom; eauto.
  iIntros "[H1 H2]".
  iApply (mapsfrom_join with "H1 H2").
Qed.

Global Instance from_sep_vmapsfrom `{!interpGS Σ} v q1 q2 ls1 ls2 :
  FromSep (v ↤?{q1+q2} (ls1 ⊎ ls2)) (v ↤?{q1} ls1) (v ↤?{q2} ls2).
Proof.
  by rewrite /FromSep vmapsfrom_join.
Qed.

Global Instance timeless_vmapsfrom `{!interpGS Σ} v q ls :
  Timeless (vmapsfrom v q ls).
Proof. destruct v; apply _. Qed.

Lemma vmapsfrom_split `{!interpGS Σ} v q1 q2 ls1 ls2 :
  (is_loc v -> q1 = 0%Qz → AllNeg ls1) ->
  (is_loc v -> q2 = 0%Qz -> AllNeg ls2) ->
  v ↤?{q1+q2} (ls1 ⊎ ls2) -∗ v ↤?{q1} ls1 ∗ v ↤?{q2} ls2.
Proof.
  destruct v; simpl vmapsfrom; eauto.
  iIntros.
  iApply mapsfrom_split; eauto.
Qed.

(* ------------------------------------------------------------------------ *)

Definition diff_loc v1 v2 : Prop :=
  match v1,v2 with
  | val_loc l1, val_loc l2 => l1 ≠ l2
  | _,_ => True end.

Lemma vmapsfrom_confront `{!interpGS Σ} v1 v2 q1 q2 ls1 ls2 b L :
  (is_loc v1 -> is_loc v2 -> 1 < q1 + q2)%Qz ->
  v1 ↤?{q1} ls1 ∗ v2 ↤?{q2} ls2 =[ b | L ]=∗ v1 ↤?{q1} ls1 ∗ v2 ↤?{q2} ls2 ∗ ⌜diff_loc v1 v2⌝.
Proof.
  iIntros (Hq) "(? & ?)". iIntros.
  destruct v1; try (simpl; iFrame; iPureIntro; easy).
  destruct v2; try (simpl; iFrame; iPureIntro; easy).
  iMod (mapsfrom_confront with "[$] [$]") as "(? & ? & ? & %Hneq)".
  { rewrite comm_L. eauto. }
  iFrame. eauto.
Qed.

Lemma vmapsfrom_cleanup `{!interpGS Σ} l' v q ls b L :
  v ↤?{q} ls ∗ †l' =[ b | L]=∗
  v ↤?{q} (ls ⊎ {[-l'-]}) ∗ †l'.
Proof.
  iIntros "[? #?]". iIntros.
  destruct v; try by iFrame.
  simpl.
  iMod (mapsfrom_cleanup with "[$] [$]") as "[? ?]".
  by iFrame.
Qed.

Lemma vmapsfrom_correct `{!interpGS Σ} v q ls :
  v ↤?{q} ls -∗ ⌜¬ is_loc v \/ (q = 0%Qz -> AllNeg ls)⌝.
Proof.
  iIntros.
  destruct v; try naive_solver.
  simpl. iDestruct (mapsfrom_correct with "[$]") as "%Hq".
  naive_solver.
Qed.

(* ------------------------------------------------------------------------ *)

(* A technical lemma, for internal use. *)

Lemma interpret_val_pointer `{interpGS Σ} v q ls :
  (is_loc v -> q <> 0%Qz) ->
  interpret (map (λ l', (l', q, ls)) (val_pointer_list v)) ≡
  (v ↤?{q} ls)%I.
Proof.
  intros.
  destruct v; simpl; rewrite ?interpret_nil ?interpret_singleton //.
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* The following technical lemma describes the ghost store update that
   takes place at the level of [ph_interp] when a value [w] is stored
   in a memory block or a stack cell, overwriting a previous value [v]. *)

(* This lemma cannot be placed in the file ph.v (even though it may seem as
   though it belongs there) because it depends on several notions that are
   specific of SpaceLang, whereas ph.v is language-agnostic. *)

(* We assume that [b] is the old block and [b'] is the new block. They
   differ by just one field, so, if the values [v] and [w] are equal,
   then [b] and [b'] are equal. If the values [v] and [w] are not
   equal, then they are not aliased (not the same memory location), so
   the pointers present in [b] but not [b'] are the pointers found in
   [v], and the pointers present in [b'] but not in [b] are the
   pointers found in [w]. *)

(* We introduce a [precise] arguments allowing to distinguish the
   case where we do not need to track predecessors. *)

Lemma ph_update_1 `{!interpGS Σ} σ l v b w b' qw lsw :
  (is_loc w -> qw <> 0%Qz) ->
  σ !! l = Some b →
  (v = w → b = b') →
  (¬ alias v w → old_pointers b b' = val_pointer_multiset v) →
  (¬ alias v w → new_pointers b b' = val_pointer_multiset w) →
  b ≠ BDeallocated →
  b' ≠ BDeallocated →
  let σ' := <[l := b']> σ in
  ph_interp σ  ∗ l ↦ b  ∗ w ↤?{qw}  lsw ==∗
  ph_interp σ' ∗ l ↦ b' ∗ w ↤?{qw} (lsw ⊎ {[+l+]}) ∗ v ↤?{0} {[-l-]}.
Proof.
  intros Hnw Hl ? Hold Hnew ? ?.
  destruct (decide (alias v w)) as [ Halias | Halias ].

  (* Case: [alias v w]. Then, the store instruction has no effect. *)
  { apply alias_implies_equal_locations in Halias.
    destruct Halias as (l' & ? & Hw).
    assert (w = v) by congruence. subst w.
    assert (b = b') by eauto. subst b'.
    intros σ'.
    assert (Hnop: σ' = σ) by (eapply insert_id; exact Hl).
    rewrite Hnop.
    subst v. simpl.
    iIntros "(? & ? & Hmf1)". iFrame. iModIntro.
    iApply mapsfrom_split_neg; try easy.
    { intros. exfalso. apply Hnw; eauto. }
    { intros. apply AllNeg_nsingleton. }
    assert (lsw ≡ lsw ⊎ {[+ l +]} ⊎ {[-l-]}) as <-.
    { rewrite -assoc disj_union_sinlgeton_opposite right_id //. }
    iFrame. }

  (* Case: [v] and [w] are not aliases, that is, not the same pointer. *)
  intros σ'.

  (* Define appropriate in and out triples. *)
  set (new_triples := map (λ l', (l', qw, lsw)) (val_pointer_list w)).

  (* Perform a ghost store update. *)
  iIntros "(Hh & Hmapsto & Hmf1)".
  iMod (ph_update σ l b b' new_triples with "[Hh Hmapsto Hmf1]")
    as "(Hh & Hmapsto & Hmf1 & Hmf2)".
  { eauto. }
  { eauto. }
  { rewrite /addresses /new_triples Hnew // map_map map_id //. }
  { rewrite /new_triples !interpret_val_pointer // insert_id //.
    iFrame. }

  (* There we are! *)
  rewrite Hold // /new_triples !map_map !interpret_val_pointer //.
  iFrame.
  rewrite /val_pointer_multiset /val_pointer_list.
  destruct v; simpl; try by iFrame.
  rewrite right_id gmultiset_elements_singleton interpret_unregister_cons.
  iDestruct "Hmapsto" as "[? ?]".
  by iFrame.
Qed.

(* ------------------------------------------------------------------------ *)

(* The following technical lemma describes (part of) the ghost store update
   that takes place when a value [w] is stored in a memory block, overwriting
   a previous value [v]. It is a special case of [ph_update_1]. *)

(* We use a [precise] argument to indicate if we track predecessors. *)

Lemma ph_store_heap `{!interpGS Σ} σ l v vs ofs w qw lsw :
  (is_loc w -> qw <> 0%Qz) ->
  σ !! l = Some (BBlock vs) →
  (0 <= ofs < length vs)%nat →
  vs !! ofs = Some v →
  let b := BBlock vs in
  let b' := BBlock (<[ ofs := w ]> vs) in
  let σ' := <[l := b']> σ in
  ph_interp σ  ∗ l ↦ b  ∗ w ↤?{qw}  lsw ==∗
  ph_interp σ' ∗ l ↦ b' ∗ w ↤?{qw} (lsw ⊎ {[+l+]}) ∗ v ↤?{0} {[-l-]}.
Proof.
  intros.
  eapply ph_update_1;  eauto using old_pointers_store_nonaliased, new_pointers_store_nonaliased.
  (* There remains to prove [v = w → b = b']. *)
  { intros <-. subst b b'. rewrite list_insert_id //. }
Qed.
