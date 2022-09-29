From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.language Require Import notation.

From spacelambda Require Import more_space_lang wp_all wpc triple.
From spacelambda.examples Require Import tactics ref list stack.

(* LATER later make_record *)

(* We encode fixed-capacity stacks as a record of an array and a size.
   We are parameterised by a capacity. *)

Module StackChunk(C:Capacity) : StackOf with
Definition capacity := Some (C.capacity)
.
Definition capacity := Some (C.capacity).
Definition capa := Pos.to_nat C.capacity.

Definition stack_empty : val :=
  λ: [[]],
    let: "c" := alloc 2 in
    let: "a" := alloc (capa) in
    "c".[0] <- "a" ;;
    "c".[1] <- 0;; (* The current size *)
    "c".

Definition stack_push : val :=
  λ: [["v", "l"]],
    let: "size" := "l".[1] in
    let: "new_size" := 1 '+ "size" in
    let: "a" := "l".[0] in
    "a".["size"] <- "v";;
    "l".[1] <- "new_size".

Definition stack_pop : val :=
  λ: [["l"]],
    let: "size" := "l".[1] in
    let: "new_size" := "size" '- 1 in
    let: "a" := "l".[0] in
    let: "v" := "a".["new_size"] in
    "a".["new_size"] <- val_unit;; (* We remove l as an antecedent *)
    "l".[1] <- "new_size";;
    "v".

Definition stack_is_empty : val :=
  λ: [["l"]],
    let: "size" := "l".[1] in
    1 '- "size".

Definition stack_is_full : val :=
  λ: [["l"]],
    let: "size" := "l".[1] in
    let: "moresize" := "size" '+ 1  in
    "moresize" '- capa.

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

Definition empty_cost : Qz := 2 + capa.
Definition cell_cost  : Qz := 0.

(* [ChunkInv A L] associates the model L with the concrete representation L. *)
Record ChunkInv (A L : list val) : Prop :=
  { chunk_front  : forall i, 0 <= i < length L -> (A !! i) = (L !! (length L - i - 1));
    chunk_tail   : forall i, length L <= i < length A -> (A !! i) = Some val_unit;
    chunk_length : length A = capa;
    chunk_correct : length L <= length A
  }.

(* [isChunk L a] *)
Definition isChunkOf `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qz * Qp))) (c:loc) : iProp Σ :=
  ∃ arr vs, c ↦ BBlock arr ∗ ⌜ChunkInv arr vs⌝ ∗ soup R {[+c+]} xs vs.

(* [Stack L s] *)
Definition StackOf `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qz * Qp))) (s:loc) : iProp Σ :=
  ∃ c i,
    s ↦ BBlock [val_loc c; val_nat i] ∗ isChunkOf R xs c ∗ Stackable c 1%Qp ∗ c ↤ {[+s+]} ∗ ⌜i = length xs⌝.

Ltac liago := try (subst; simpl; lia).

Ltac destruct_stack Hs :=
  iDestruct Hs as "[%c [%i (Hs & Hc & ? & ? & %Hi)]]".

Ltac destruct_chunk Ha :=
  iDestruct Ha as "[%arr [%vs [? [%AInv Hmfa]]]]".

Lemma lengtho_neq_zero_iff_nil A (xs:list A) :
  1 - length xs ≠ 0 ↔ xs = [].
Proof. now destruct xs. Qed.

Lemma stack_is_empty_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun n => ⌜n ≠ 0 <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs". destruct_stack "Hs". destruct_chunk "Hc".
  wps_nofree.
  iStepsS.
  eauto using lengtho_neq_zero_iff_nil.
Qed.

Lemma stack_is_full_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun n => ⌜n ≠ 0 <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs". destruct_stack "Hs". destruct_chunk "Hc".
  wps_nofree.
  iStepsS.
  destruct AInv as [_ _ ? Hco].
  unfold capa in *. liago.
Qed.

Lemma ChunkInv_init :
  ChunkInv (replicate capa val_unit) nil.
Proof.
  constructor; try rewrite replicate_length; try easy; simpl.
  { intros. rewrite lookup_replicate; split; easy. }
  { lia. }
Qed.

Lemma stack_empty_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ Stackable s 1%Qp ∗ s ↤ ∅).
Proof.
  iIntros.
  wps_call.
  wps_bind. rewrite /empty_cost.
  wps_alloc l as "(? & ? & ? & ?)".
  wps_context l.
  wps_bind. wps_alloc l' as  "(? & ? & ? & ?)".
  wps_bind. wps_store.
  wps_bind. wps_store.
  wps_val. iIntros. iFrame. iExists _,_.
  iFrame. rewrite left_id. iFrame.
  iSplitL; try easy.
  iExists _,nil. iFrame. simpl.
  iSplitR.
  { iPureIntro. apply ChunkInv_init. }
  { iApply soup_empty. }
Qed.

Lemma ChunkInv_pop A v vs i :
  i = length vs ->
  ChunkInv A (v :: vs) ->
  ChunkInv (<[i:=()%V]> A) vs.
Proof.
  intros ? [Af At ? Ac].
  constructor.
  { intros j Hj. specialize (Af j).
    simpl in Af.
    rewrite list_lookup_insert_ne; liago.
    rewrite Af; liago.
    rewrite lookup_cons_ne_0; liago.
    f_equal. liago. }
  { intros j Hj. rewrite insert_length in Hj.
    destruct (decide (j=i)) as [->|].
    { rewrite list_lookup_insert //. liago. }
    { rewrite list_lookup_insert_ne //.
      rewrite At //. liago. } }
  { rewrite insert_length //. }

  { rewrite insert_length. simpl in *. liago. }
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
  wps_load.
  wps_bind.
  iStepS. iStepS.
  wps_bind.
  wps_load.
  wps_context c.
  wps_bind.

  destruct_chunk "Hc".
  iDestruct (big_sepL2_length with "[$]") as "%Hl".
  assert (0 <= (S (length xs)) - 1 < length arr) as HAi.
  { destruct AInv as [_ _ _ Hco].
    subst. simpl in *. liago. }

  iDestruct (big_sepL2_cons_inv_l with "[$]") as
    "[%v [%vs' (%Heq & ((? & ? & ?) & ?))]]". subst vs.

  assert (arr !! ((S (length xs)) - 1) = Some v) as HAv.
  { destruct AInv as [Af _ _ _].
    rewrite Af. simpl in *.
    { assert ((S (length vs') - (length xs - 0) - 1) = 0) as -> by lia.
      easy. }
    { simpl in *. liago. } }
  simpl.

  wps_load.
  rewrite list_lookup_total_alt HAv. simpl.
  wps_context v.
  wps_bind. wps_store.
  wps_bind. wps_store.
  rewrite list_lookup_total_alt HAv. simpl.

  iApply wps_bupd. iMod diamonds_zero. iModIntro.
  wps_val. iIntros. iFrame.

  iDestruct (vmapsfrom_join with "[$]") as "?".
  rewrite left_id. assert ({[-c-]} ⊎ {[+ c +]} ≡ ∅) as -> by smultiset_solver.
  unfold cell_cost. rew_qz.
  iFrame.

  iExists _,_.
  iFrame.
  iSplitL.
  2:{ iStepsS. }
  iExists _,_. iFrame.

  iPureIntro.
  eapply ChunkInv_pop; eauto.
  lia.
Qed.

Lemma ChunkInv_push A v vs i :
  length vs < capa ->
  i = length vs ->
  ChunkInv A vs ->
  ChunkInv (<[i:=v]> A) (v :: vs).
Proof.
  intros ? ? [Af At ? Hc].
  constructor.
  { intros j Hj. simpl in Hj.
    destruct (decide (j=i)) as [->|].
    { rewrite list_lookup_insert; liago.
      simpl. assert ((S (length vs) - i - 1) = 0) as -> by lia.
      rewrite lookup_cons //. }
    { rewrite list_lookup_insert_ne //.
      rewrite lookup_cons_ne_0; liago.
      rewrite Af; liago.
      f_equal. liago. } }
  { intros j Hj. rewrite insert_length in Hj. simpl in Hj.
    destruct (decide (j=i)).
    { exfalso. lia. }
    { rewrite list_lookup_insert_ne //.
      rewrite At //. liago. } }
  { rewrite insert_length //. }
  { rewrite insert_length. liago. }
Qed.

Lemma stack_push_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) s qp qz v x xs :
  size_lt (length xs) capacity ->
  qz ≠ 0%Qz ->
  CODE (stack_push [[v, s]])
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅)
  POST (fun tt => StackOf R ((x,(qz,qp))::xs) s).
Proof.
  unfold size_lt, capacity.
  iIntros (? ?) "(_ & Hs & ? & ? & ?)".
  destruct_stack "Hs".
  wps_call.
  wps_bind. wps_load. iIntros.
  wps_bind. wps_bin_op. iIntros.
  wps_bind. wps_load. iIntros.

  destruct_chunk "Hc".
  assert (0 <= length xs < length arr) as ?.
  { destruct AInv as [_ _ Hcl _]. unfold capa in *. liago. }

  iDestruct (big_sepL2_length with "[$]") as "%Hl".

  assert (arr !! (length xs) = Some ()%V).
  { destruct AInv as [_ -> _ _]; try easy.
    liago. }

  wps_bind. simpl. wps_store.
  rewrite left_id. rew_enc.

  do 6 iStepS. iFrame.
  iExists _,_. iFrame.
  iSplitL; try easy.
  iExists _,(v::vs). iFrame.
  iPureIntro.
  apply ChunkInv_push; eauto; unfold capa; liago.
Qed.

Lemma stack_free `{!interpGS Σ} A (R:A -> val -> iProp Σ) s xs :
  Stackable s 1%Qp ∗ s ↤ ∅ ∗ StackOf R xs s =#=∗
  ♢(empty_cost+cell_cost*length xs) ∗ †s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(Hcs' & Hfs & Hs)". iIntros.
  destruct_stack "Hs".

  iMod (@logical_free _ _ _ _ s with "[$] [$]") as "(? & ? &#Hs)"; try easy.
  iMod (mapsfrom_cleanup with "[$] [$]") as "(? & ?)".
  rewrite disj_union_sinlgeton_opposite.

  destruct_chunk "Hc".
  iMod (logical_free with "[$] [$]") as "(? & ? & ?)"; try easy.
  iMod (soup_cleanup with "[$] [$]") as "(? & ? & ?)".
  iDestruct (diamonds_join with "[$]") as "Hdiams".
  iFrame "Hs". iModIntro. iFrame.
  iSplitL "Hdiams". iFrame.
  { simpl. destruct AInv as [? ? -> ?].
    rewrite /empty_cost /cell_cost.
    conclude_diamonds. }
  { iExists _. unfold soup. iFrame. }
Qed.

End StackChunk.
