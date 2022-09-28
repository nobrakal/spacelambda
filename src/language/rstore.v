From stdpp Require Import sets mapset gmultiset gmap relations.
From iris.program_logic Require Import language.

From glaneur.spacelang Require Import successors.
From glaneur Require Import rhypotheses syntax head_semantics pointers.

Set Implicit Arguments.

Global Notation dom := (dom (gset loc)).

(* ------------------------------------------------------------------------ *)
(* We want to reuse as much code as possible from the spacelang project.
   They use a store distinguishing root blocks from others.
   Therefore we design a reification, annotating root blocks as such. *)

Inductive rblock :=
| RRoot  : list val -> rblock (* A root *)
| RBlock : list val -> rblock (* A block *)
| RDeallocated : rblock. (* The deallocated root *)

Global Instance rblock_inhabited : Inhabited rblock :=
  populate RDeallocated.

(** Conversions *)
Definition of_rblock (r:rblock) : block :=
  match r with
  | RRoot b | RBlock b => BBlock b
  | RDeallocated => BDeallocated end.

Definition to_rblock (roots:gset loc) (l:loc) (b:block) : rblock :=
  match b with
  | BDeallocated => RDeallocated
  | BBlock b =>
      if decide (l ∈ roots)
      then RRoot b
      else RBlock b end.

(** is_root *)
Definition rblock_is_root (b:rblock) : Prop :=
  match b with
  | RRoot _ => True
  | _ => False end.

Definition decide_rblock_is_root b : {rblock_is_root b} + {¬ (rblock_is_root b)}.
Proof.
  destruct b; [by left | right | right]; eauto.
Defined.

Global Instance decision_rblock_is_root b :
  Decision (rblock_is_root b) := decide_rblock_is_root b.

(** RHypotheses instance *)
Definition rblock_pointer_set b : gmultiset loc :=
  list_to_set_disj (block_pointer_list (of_rblock b)).

(* Theses richer blocks satisfy the "hypotheses" *)
Global Instance lang_hypotheses : @Hypotheses loc _ _ rblock _.
Proof.
  exists rblock_pointer_set RDeallocated; try easy.
  intros []; [now right|now right |now left].
Defined.

Global Instance lang_rhypotheses : @RHypotheses loc _ _ rblock _ _.
Proof.
  exists rblock_is_root; try easy.
  apply _.
Defined.

(** We can convert a store to a "rooted store" *)
Definition to_rstore (roots:gset loc) (s:store) :=
  map_imap (fun l b => Some (to_rblock roots l b)) s.

Definition size_rblock (r:rblock) :=
  size_block (of_rblock r).

(* ------------------------------------------------------------------------ *)
(* For rewriting *)

Lemma rblock_of_to k l b :
  (of_rblock (to_rblock k l b)) = b.
Proof.
  destruct b; try easy. unfold to_rblock.
  by destruct (decide (l ∈ k)).
Qed.

Lemma rblock_to_of k l r :
  (rblock_is_root r <-> l ∈ k /\ r <> deallocated) ->
  to_rblock k l (of_rblock r) = r.
Proof.
  intros (Hr1&Hr2).
  unfold to_rblock, of_rblock.
  destruct r; try easy.
  { destruct (decide (l ∈ k)); try easy.
    exfalso.
    by destruct Hr1. }
  { destruct (decide (l ∈ k)); try easy.
    exfalso.
    by destruct Hr2. }
Qed.

Lemma rblock_pointer_set_eq k l b :
  rblock_pointer_set (to_rblock k l b) = block_pointer_set b.
Proof.
  unfold block_pointer_set, rblock_pointer_set.
  f_equal. by rewrite rblock_of_to.
Qed.

Lemma rblock_pointers_eq k l b :
  pointers (to_rblock k l b) = pointers b.
Proof.
  unfold pointers. simpl.
  by rewrite rblock_pointer_set_eq.
Qed.

Lemma rblock_pointer_set_root bs :
  rblock_pointer_set (RRoot bs) = block_pointer_set (BBlock bs).
Proof. easy. Qed.

Lemma rblock_pointer_set_block bs :
  rblock_pointer_set (RBlock bs) = block_pointer_set (BBlock bs).
Proof. easy. Qed.

(** Inversion & equality *)

Lemma to_rstore_init r :
  to_rstore r ∅ = ∅.
Proof. easy. Qed.

Lemma dom_to_rstore k σ :
  dom (to_rstore k σ) = dom σ.
Proof.
  apply leibniz_equiv.
  apply dom_imap.
  split.
  { intros. exists (σ !!! i).
    split; try easy.
    by apply lookup_lookup_total_dom. }
  { intros (?,(?&_)).
    by eapply elem_of_dom_2. }
Qed.

Lemma to_rblock_eq_inv k l e e' :
  to_rblock k l e = to_rblock k l e' ->
  e = e'.
Proof.
  intros E.
  apply (@f_equal _ _ of_rblock) in E.
  by do 2 rewrite rblock_of_to in E.
Qed.

Lemma lookup_to_rstore (k:gset loc) (σ:gmap loc block) (l:loc) :
  to_rstore k σ !! l = fmap (to_rblock k l) (σ !! l).
Proof.
  unfold to_rstore.
  rewrite map_lookup_imap.
  by destruct (σ !! l).
Qed.

Lemma lookup_total_to_rstore k σ l :
  (to_rstore k σ) !!! l = to_rblock k l (σ !!! l).
Proof.
  do 2 rewrite lookup_total_alt.
  rewrite lookup_to_rstore.
  by destruct (σ !! l).
Qed.

Lemma to_rblock_dealloacted_inv k l b :
  to_rblock k l b = RDeallocated ->
  b = BDeallocated.
Proof.
  unfold to_rblock.
  destruct b; try easy.
  by destruct (decide (l ∈ k)).
Qed.

Lemma to_rblock_in k l vs :
  l ∈ k ->
  to_rblock k l (BBlock vs) = RRoot vs.
Proof.
  intros ?.
  unfold to_rblock.
  by destruct (decide (l ∈ k)).
Qed.

Lemma to_rblock_eq_root k l b v :
  to_rblock k l b = RRoot v ->
  l ∈ k /\ b = BBlock v.
Proof.
  destruct b; try easy.
  unfold to_rblock.
  destruct (decide (l ∈ k)); try easy.
  intros R; injection R; by intros ->.
Qed.

Lemma to_rblock_notin k l vs :
  l ∉ k ->
  to_rblock k l (BBlock vs) = RBlock vs.
Proof.
  unfold to_rblock; intros ?.
  by destruct (decide (l ∈ k)).
Qed.

Lemma to_rblock_eq_block k l b vs :
  to_rblock k l b = RBlock vs ->
  l ∉ k.
Proof.
  unfold to_rblock; intros ?.
  destruct b; try easy.
  by destruct (decide (l ∈ k)).
Qed.

Lemma to_rstore_read_deallocated k l σ :
  to_rstore k σ !!! l = RDeallocated <->
    σ !!! l = BDeallocated.
Proof.
  rewrite lookup_total_to_rstore.
  rewrite lookup_total_alt.
  split; intros E;
    destruct (σ !! l); simpl in *; subst; try easy.
  eauto using to_rblock_dealloacted_inv.
Qed.

Lemma to_rstore_preserves_successors k1 k2 σ l :
  successors (to_rstore k1 σ) l =
    successors (to_rstore k2 σ) l.
Proof.
  unfold successors.
  do 2 rewrite map_lookup_imap.
  destruct (σ !! l); try easy. simpl.
  by do 2 rewrite rblock_pointer_set_eq.
Qed.

Lemma to_rstore_preserves_successor k1 k2 σ l l' :
  successor (to_rstore k1 σ) l l' <->
    successor (to_rstore k2 σ) l l'.
Proof.
  unfold successor.
  by erewrite to_rstore_preserves_successors.
Qed.

Lemma to_rstore_insert k l b s :
  to_rstore k (<[l:=b]> s) = <[l:=to_rblock k l b]> (to_rstore k s).
Proof.
  unfold to_rstore.
  by rewrite map_imap_insert.
Qed.

Lemma to_rstore_not_in k l s :
  s !! l = None ->
  to_rstore (k ∪ {[l]}) s = to_rstore k s.
Proof.
  intros E.
  apply map_eq. intros l'.
  do 2 rewrite lookup_to_rstore.
  destruct (s !! l') eqn:Hl'; try easy. simpl.
  f_equal. unfold to_rblock.
  destruct b; try easy.
  case (decide (l' ∈ k ∪ {[l]})); intros Hl''; try easy.
  { apply elem_of_union in Hl''.
    destruct Hl''.
    { by destruct (decide (l' ∈ k)). }
    apply elem_of_singleton in H. subst.
    exfalso. congruence. }
  { apply not_elem_of_union in Hl''. destruct Hl''.
    by (destruct (decide (l' ∈ k))). }
Qed.

(* ------------------------------------------------------------------------ *)
(* Converse direction *)

Definition of_rstore (s:gmap loc rblock) : gmap loc block :=
  fmap of_rblock s.

Lemma rstore_to_of (k:gset loc) (σ : gmap loc rblock) :
  (forall l r, σ !! l = Some r  -> rblock_is_root r <-> l ∈ k /\ r <> deallocated) ->
  to_rstore k (of_rstore σ) = σ.
Proof.
  intros Hrd.
  apply map_eq.
  intros l.
  rewrite map_lookup_imap.
  rewrite lookup_fmap.
  destruct (σ !! l) eqn:E; try easy.
  simpl. f_equal.

  apply rblock_to_of.
  by apply Hrd.
Qed.

Lemma size_rblock_to_rblock k l x :
  size_rblock (to_rblock k l x) = size_block x.
Proof.
  unfold size_rblock.
  by rewrite rblock_of_to.
Qed.

Definition size_rstore (s:gmap loc rblock) : nat :=
  map_fold (fun l b acc => acc + size_rblock b)%nat 0%nat s.

Lemma size_rstore_to_rstore k σ :
  size_rstore (to_rstore k σ) = size_heap σ.
Proof.
  pose (P:= (fun σ => size_rstore (to_rstore k σ) = size_heap σ)).
  apply (map_ind P); unfold P; clear P.
  { easy. }
  intros l x m Hix IH.
  unfold size_rstore, to_rstore, size_heap in *.
  rewrite map_fold_insert; try easy.
  { rewrite map_imap_insert.
    rewrite map_fold_insert.
    { by rewrite IH size_rblock_to_rblock. }
    { intros. lia. }
    { apply not_elem_of_dom.
      rewrite dom_imap.
      { apply not_elem_of_dom in Hix. apply Hix. }
      {  intros ?. split.
         { intros Hi.
           apply elem_of_dom in Hi. destruct Hi.
           eauto. }
         { intros (?,(?&?)). apply elem_of_dom. eauto. } } } }
  { lia. }
Qed.

Lemma size_block_of_rblock x :
  size_block (of_rblock x) = size_rblock x.
Proof. easy. Qed.

Lemma size_heap_of_rstore σ :
  size_heap (of_rstore σ) = size_rstore σ.
Proof.
  pose (P:= (fun σ => size_heap (of_rstore σ) = size_rstore σ)).
  apply (map_ind P); unfold P; clear P.
  { easy. }
  intros l x m Hix IH.
  unfold size_rstore, of_rstore, size_heap in *.
  rewrite map_fold_insert; try easy.
  { rewrite fmap_insert.
    rewrite map_fold_insert.
    { by rewrite IH size_block_of_rblock. }
    { lia. }
    { apply not_elem_of_dom.
      rewrite dom_fmap.
      by apply not_elem_of_dom. } }
  { lia. }
Qed.

(* ------------------------------------------------------------------------ *)
(* no_reachable_freed *)

Definition no_reachable_freed σ :=
  forall l, reachable σ l -> σ !! l <> Some RDeallocated.

Lemma no_reachable_freed_init :
  no_reachable_freed (to_rstore ∅ ∅).
Proof.
  rewrite to_rstore_init. intros ? ?.
  rewrite lookup_empty //.
Qed.

Lemma rno_reachable_freed r σ :
  closed (to_rstore r σ) ->
  no_reachable_freed (to_rstore r σ) ->
  forall l, reachable (to_rstore r σ) l -> σ !! l <> Some BDeallocated.
Proof.
  unfold no_reachable_freed.
  intros ? Hn l Hrl. generalize Hrl. intros E.
  apply Hn in Hrl.
  assert (l ∈ dom σ).
  { rewrite -(dom_to_rstore r).
    eauto using closed_reachable_in_dom. }
  rewrite lookup_to_rstore in Hrl.
  destruct (σ !! l) eqn:E'.
  2:{ apply not_elem_of_dom in E'. easy. }
  intros I. injection I. intros ->. easy.
Qed.

Lemma locs_insert n v (bs:list val) :
  locs (<[n:=v]> bs) ⊆ locs v ∪ locs bs.
Proof.
  auto_locs. rewrite /location_list /locs_list.
  rewrite list_fmap_insert /union_list.
  revert n. induction bs; try easy.
  intros n. simpl.
  destruct n; multiset_solver.
Qed.

Lemma block_pointer_set_insert l n bs v :
  l ∈ pointers (RRoot (<[n:=v]> bs)) ->
  l ∈ locs v \/ l ∈ pointers (RRoot bs).
Proof.
  intros E.
  apply pointers_locs in E. rewrite -pointers_locs.
  apply locs_insert in E.
  set_solver.
Qed.
