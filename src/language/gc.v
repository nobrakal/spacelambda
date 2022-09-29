Require Import Coq.Program.Equality.
From stdpp Require Import sets mapset gmap relations gmultiset.
From iris.program_logic Require Import language.

From spacelambda.spacelang Require Import stdpp hypotheses successors.
From spacelambda Require Import store rstore pointers.

Set Implicit Arguments.

(* This file defines garbage collection in spacelambda. *)

(* ------------------------------------------------------------------------ *)

(* Most of the work of defining garbage collection is already done in the
   file [successors.v], where the relation [store_evolution] on stores is
   defined. Here, this relation is extended in a trivial way to machine
   stores. *)

(* The work in [successors.v] is done with annotated roots inside the store
   (the so-called stack cells). There we annotate them with our roots. *)
Definition gc roots (σ1 σ2 : store) :=
  store_evolution (to_rstore roots σ1) (to_rstore roots σ2).

Local Hint Unfold gc : core.

(* ------------------------------------------------------------------------ *)
(* Basic lemmas about [gc] *)

(* The GC may have no effect. *)
Lemma gc_id r σ :
  gc r σ σ.
Proof.
  eauto using store_evolution_reflexive.
Qed.

(* The GC is transitive. *)
Lemma gc_trans r σ1 σ2 σ3 :
  gc r σ1 σ2 ->
  gc r σ2 σ3 ->
  gc r σ1 σ3.
Proof.
  eauto using store_evolution_transitive.
Qed.

(* gc preserves domain *)
Lemma gc_dom r σ1 σ2 :
  gc r σ1 σ2 ->
  dom σ1 = dom σ2.
Proof.
  unfold gc. intros [Hd].
  repeat rewrite dom_to_rstore in Hd.
  by apply leibniz_equiv.
Qed.

Lemma gc_inv_empty r σ :
  gc r ∅ σ ->
  σ = ∅.
Proof.
  intros Hgc.
  apply gc_dom in Hgc. rewrite dom_empty_L in Hgc.
  apply dom_empty_iff.
  rewrite Hgc //.
Qed.

(* ------------------------------------------------------------------------ *)
(* We want to derive [gc_weak]. We have to work a bit. *)

Lemma is_root_to_rstore r σ l :
  is_root (to_rstore r σ) l <-> l ∈ r /\ σ !!! l <> BDeallocated.
Proof.
  unfold is_root.
  rewrite lookup_total_alt map_lookup_imap.
  split.
  { intros (b,(Hr&Hb)).
    destruct (σ !! l); simpl in *; try easy.
    injection Hr. intros. subst.
    destruct b0; try easy. split; try easy.
    unfold rblock_is_root, to_rblock in Hb.
    by destruct (decide (l ∈ r)). }
  { intros (?&?).
    destruct (σ !! l) as [[vs|]|]; try easy.
    exists (RRoot vs). simpl.
    destruct (decide (l ∈ r)); easy. }
Qed.

Lemma gc_preserves_is_root_to_rstore r σ1 σ2 l:
  gc r σ1 σ2 ->
  is_root (to_rstore r σ1) l ->
  is_root (to_rstore r σ2) l.
Proof.
  unfold gc. intros.
  by rewrite <- store_evolution_preserves_is_root.
Qed.

Lemma to_rstore_roots_mono r1 r2 σ l :
  r1 ⊆ r2 ->
  is_root (to_rstore r1 σ) l ->
  is_root (to_rstore r2 σ) l.
Proof.
  do 2 rewrite is_root_to_rstore.
  intros ? (?&?).
  eauto.
Qed.

Lemma rtc_successors_successor σ σ' r d :
  (forall l, successors σ l = successors σ' l) ->
  rtc (successor σ) r d ->
  rtc (successor σ') r d.
Proof.
  intros Hs.
  eapply rtc_subrel. intros.
  unfold successor in *.
  by rewrite -Hs.
Qed.

Lemma to_rstore_mono_reachable_finer r1 r2 r σ l :
  r1 ⊆ r2 ->
  r ∈ r1 ->
  rtc (successor (to_rstore r1 σ)) r l ->
  rtc (successor (to_rstore r2 σ)) r l.
Proof.
  intros.
  eauto using rtc_successors_successor,to_rstore_preserves_successors.
Qed.

Lemma to_rstore_mono_reachable r1 r2 σ l :
  r1 ⊆ r2 ->
  reachable (to_rstore r1 σ) l ->
  reachable (to_rstore r2 σ) l.
Proof.
  intros ? (r,(?&?)).
  exists r. split; try easy.
  { eauto using to_rstore_roots_mono. }
  { eauto using rtc_successors_successor,to_rstore_preserves_successors.  }
Qed.

(* We can weaken a set of roots. *)
(* Order of arguments helps proof search *)
Lemma gc_weak r1 r2 σ σ' :
  gc r2 σ σ' ->
  r1 ⊆ r2 ->
  gc r1 σ σ'.
Proof.
  unfold gc, store_evolution.
  repeat rewrite dom_to_rstore.
  intros [Hdom Hr] ?.
  split; try easy.
  intros ? Hl.
  destruct (Hr _ Hl) as [Hlo|(?&Hde)]; [left|right].
  { do 2 rewrite lookup_total_to_rstore in Hlo.
    do 2 rewrite lookup_total_to_rstore.
    apply to_rblock_eq_inv in Hlo.
    by rewrite Hlo. }
  { split.
    { eauto using to_rstore_mono_reachable. }
    { apply to_rstore_read_deallocated in Hde.
      by apply to_rstore_read_deallocated. } }
Qed.

(* ------------------------------------------------------------------------ *)
(* GC does not increase size. *)

Lemma block_evolution_non_size_increasing unreachable (b b':rblock) :
  block_evolution unreachable b b' →
  size_rblock b' ≤ size_rblock b.
Proof.
  destruct 1 as [ | (? & ?) ]; subst; compute; lia.
Qed.

Lemma gc_non_size_increasing r σ σ' :
  gc r σ σ' ->
  size_heap σ' ≤ size_heap σ.
Proof.
  intros [Hdom Hl].
  do 2 rewrite dom_to_rstore in Hdom.
  rewrite /size_heap.
  eapply map_fold_ind_2 with (P := λ size1 size2 m1 m2, size1 ≤ size2); try lia.
  { split; now apply None_equiv. }
  { intros l b1 b2 s1 s2 size1 size2 _ _ Hindom1 Hindom2 ?.
    assert (l ∈ dom σ) as Hlh.
    { erewrite elem_of_dom, Hindom2. eauto. }
    specialize (Hl l). rewrite dom_to_rstore in Hl.
    specialize (Hl Hlh).
    apply block_evolution_non_size_increasing in Hl.
    unfold size_rblock in *.
    do 2 rewrite lookup_total_to_rstore rblock_of_to in Hl.
    do 2 (erewrite lookup_total_correct in Hl; eauto).
    lia. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Now two "related" stores. *)

(* Similarly, the relation [store_agreement] on stores is extended in a
   trivial way to machine stores. *)
Definition related roots (σ θ : store) :=
  store_agreement (to_rstore roots σ) (to_rstore roots θ).

Local Hint Unfold related : core.

(* ------------------------------------------------------------------------ *)
(* Basic lemmas about related. *)

Lemma related_dom r (σ θ:store) :
  related r σ θ ->
  dom σ = dom θ.
Proof.
  intros [Hd].
  repeat rewrite dom_to_rstore in Hd.
  by apply leibniz_equiv.
Qed.

Lemma related_reflexive r σ :
  related r σ σ.
Proof. now constructor. Qed.

Lemma related_symmetric r (σ θ:store) :
  related r σ θ ->
  related r θ σ.
Proof.
  eauto using store_agreement_symmetric.
Qed.

Lemma prove_reachable_root l r bs s:
  l ∈ r ->
  s !! l = Some (BBlock bs) ->
  reachable (to_rstore r s) l.
Proof.
  intros Hlr Hb.
  exists l. split; try easy.
  apply is_root_to_rstore.
  rewrite lookup_total_alt Hb.
  easy.
Qed.

Lemma related_read_reachable l b r σ θ :
  reachable (to_rstore r σ) l ->
  related r σ θ ->
  θ !! l = Some b ->
  σ !! l = Some b.
Proof.
  intros Hl Hag Hb.
  assert ((to_rstore r σ) !! l = Some (to_rblock r l b)) as Hroot.
  { eapply store_agreement_at_reachable_cell.
    { apply Hag. }
    { apply Hl. }
    rewrite lookup_to_rstore.
    by rewrite Hb. }
  rewrite lookup_to_rstore in Hroot.
  destruct (σ !! l); try easy.
  injection Hroot. intros E.
  apply to_rblock_eq_inv in E.
  subst; easy.
Qed.

Lemma related_read_root l bs r σ θ :
  l ∈ r ->
  related r σ θ ->
  θ !! l = Some (BBlock bs) ->
  σ !! l = Some (BBlock bs).
Proof.
  intros.
  eapply related_read_reachable; eauto.
  eapply store_agreement_preserves_reachable; eauto.
  eauto using prove_reachable_root.
Qed.

(* ------------------------------------------------------------------------ *)
(* Toward [related_available] *)

(* This lemma is largely taken from SL *)
Lemma store_agreement_size_heap s1 s2 :
  store_agreement s1 s2 →
  size_rstore (collect s1) ≤ size_rstore s2.
Proof.
  intros Hag.
  rewrite /size_heap /collect.
  eapply map_fold_ind_2 with (P := λ size1 size2 m1 m2, size1 ≤ size2).
  { lia. }
  { lia. }
  { intros i.
    destruct Hag as (Hd, _).
    transitivity (s1 !! i = None).
    - rewrite map_lookup_imap.
      destruct (s1 !! i); split; discriminate || auto.
    - split; apply None_equiv; auto. }
  { lia. }
  intros l b1 b2 s'1 s'2 size1 size2.
  intros ? ? Himap ? ?.
  rewrite map_lookup_imap in Himap.
  case_eq (s1 !! l); [
    intros b Hsome; rewrite Hsome in Himap; simpl in Himap
  | intros Hnone; rewrite Hnone in Himap; simpl in Himap; discriminate ].
  unfold collect_block in Himap. simplify_eq.
  case (decide (reachable s1 l)).
  { intros Hreachable.
    destruct Hag as (_ & _ & Hag).
    specialize (Hag l Hreachable).
    erewrite -> !lookup_total_correct in Hag by eauto. subst.
    lia. }
  { intros _.
    unfold size_rblock. simpl. lia. }
Qed.

(* [collect] is defined on rstore, we have to do conversions. *)
Definition rcollect r σ :=
  of_rstore (collect (to_rstore r σ)).

Definition collect_block' σ l b :=
  if decide (reachable σ l) then b else deallocated.

Lemma lookup_collect σ l :
  (collect σ) !! l = fmap (collect_block' σ l) (σ !! l).
Proof.
  unfold collect.
  rewrite map_lookup_imap.
  by destruct (σ !! l).
Qed.

Lemma to_rstore_rcollect r σ :
  to_rstore r (rcollect r σ) = collect (to_rstore r σ).
Proof.
  unfold rcollect.
  rewrite rstore_to_of; try easy.
  intros l rb E.
  rewrite lookup_collect in E.
  rewrite lookup_to_rstore in E.
  destruct (σ !! l) eqn:Hl; simpl in *; try easy.
  injection E. clear E. intros E. rewrite <- E.
  simpl.

  unfold rblock_is_root, collect_block' in *.
  destruct (decide (reachable (to_rstore r σ) l)); try easy.
  rewrite E.
  split; destruct rb; try easy; intros.
  { now apply to_rblock_eq_root in E. }
  { now eapply to_rblock_eq_block in E. }
Qed.

Lemma gc_collect r σ :
  gc r σ (rcollect r σ).
Proof.
  unfold gc.
  rewrite to_rstore_rcollect.
  apply store_evolution_collect.
Qed.

Lemma related_available r σ θ :
  related r σ θ ->
  exists σ', gc r σ σ' ∧ size_heap σ' <= size_heap θ.
Proof.
  intros Hr.
  exists (rcollect r σ).
  split.
  { eauto using gc_collect. }
  { unfold available. simpl.
    apply store_agreement_size_heap in Hr.
    rewrite size_rstore_to_rstore in Hr.
    rewrite size_heap_of_rstore.
    lia. }
Qed.

(* ------------------------------------------------------------------------ *)
(* We want to derive [related_weak]. We have to work a bit. *)

Lemma store_agreement_weak_root r1 r2 σ θ l :
  r1 ⊆ r2 ->
  related r2 σ θ ->
  is_root (to_rstore r1 σ) l ->
  is_root (to_rstore r1 θ) l.
Proof.
  intros Hi [_ [_ Hr]].
  intros Hl.
  assert (reachable (to_rstore r2 σ) l) as Hrl.
  { exists l. split; try easy.
    by eapply to_rstore_roots_mono. }
  { apply Hr in Hrl.
    do 2 rewrite lookup_total_to_rstore in Hrl.
    apply to_rblock_eq_inv in Hrl.
    destruct Hl as (b,(Hl,?)).
    do 2 rewrite lookup_total_alt in Hrl.
    rewrite map_lookup_imap in Hl.
    destruct (σ !! l); try easy. injection Hl. intros. subst.
    exists (to_rblock r1 l b0); split; try easy.
    rewrite map_lookup_imap. destruct (θ !! l); simpl in *;
      subst; easy. }
Qed.

Lemma store_agreement_weak_reachable r1 r2 σ θ l :
  r1 ⊆ r2 ->
  related r2 σ θ ->
  reachable (to_rstore r1 σ) l ->
  reachable (to_rstore r1 θ) l.
Proof.
  intros Hi Hs (r,(Hr,Hl)).
  eapply to_rstore_mono_reachable_finer in Hl;
    try apply Hi.
  { apply store_agreement_preserves_reachable_path
      with (s2:=(to_rstore r2 θ)) in Hl;
      try easy.
    { exists r. split; eauto using store_agreement_weak_root.
      eapply rtc_successors_successor; try apply Hl.
      eauto using to_rstore_preserves_successors. }
    { exists r.
      eauto using store_agreement_weak_root,
        rtc_refl,to_rstore_roots_mono. } }
  { apply is_root_to_rstore in Hr.
    by destruct Hr. }
Qed.

Lemma related_weak r1 r2 σ θ :
  related r2 σ θ ->
  r1 ⊆ r2 ->
  related r1 σ θ.
Proof.
  intros Hs Hi. generalize Hs.
  intros [Hd [Hr1 Hr2]].
  repeat rewrite dom_to_rstore in Hd.
  constructor.
 { by repeat rewrite rstore.dom_to_rstore. }
  split.
  { split; eauto using store_agreement_weak_reachable,store_agreement_symmetric. }
  { intros l Hl.
    eapply to_rstore_mono_reachable in Hl; try apply Hi.
    apply Hr2 in Hl.
    do 2 rewrite lookup_total_to_rstore in Hl.
    do 2 rewrite lookup_total_to_rstore.
    by rewrite (to_rblock_eq_inv _ _ _ _ Hl). }
Qed.


(* ------------------------------------------------------------------------ *)
(* Closing. *)

Definition closed_from r (σ:store) :=
  closed (to_rstore r σ).

Lemma closed_from_change r1 r2 σ :
  closed_from r1 σ ->
  closed_from r2 σ.
Proof.
  unfold closed_from, closed.
  intros Hclo l l' Hll'.
  eapply to_rstore_preserves_successor in Hll'.
  apply Hclo in Hll'.
  rewrite dom_to_rstore in Hll'.
  by rewrite dom_to_rstore.
Qed.

(* The set of roots does not import when closing. *)
Definition closed σ := closed_from ∅ σ.

Lemma closed_init :
  closed ∅.
Proof.
  intros ? ? E. exfalso.
  rewrite to_rstore_init /successor /successors lookup_empty in E.
  set_solver.
Qed.

Lemma closed_closed_from r σ :
  closed σ ->
  closed_from r σ.
Proof. intros. eapply closed_from_change. eauto. Qed.

(* ------------------------------------------------------------------------ *)
(* A very useful invariant. *)

Definition valid_roots (r:gset loc) (σ:store) :=
  forall l, l ∈ r -> l ∈ dom σ /\ σ !! l <> Some BDeallocated.

Lemma valid_roots_init:
  valid_roots ∅ ∅.
Proof. intros ?. set_solver. Qed.

Lemma prove_reachable_valid_root l r σ :
  l ∈ r ->
  valid_roots r σ ->
  reachable (to_rstore r σ) l.
Proof.
  intros Hl Hv.
  generalize Hl. intros ?.
  apply Hv in Hl. destruct Hl.
  exists l. split; try easy.
  apply is_root_to_rstore. split; try easy.
  rewrite lookup_total_alt.
  destruct (σ !! l) as [b|] eqn:E; try easy.
  2:{ by apply not_elem_of_dom in E. }
  by destruct b.
Qed.

Lemma valid_roots_free l (r:gset loc) σ :
  l ∉ r ->
  valid_roots r σ ->
  valid_roots r (<[l:=BDeallocated]> σ).
Proof.
  intros ? Hr l' Hl'. simpl.
  assert (l <> l') by set_solver.
  apply Hr in Hl'. destruct Hl' as (?&?).
  split. set_solver.
  by rewrite lookup_insert_ne.
Qed.

Lemma valid_roots_free_group locs (r:gset loc) σ :
  locs ⊆ dom σ ->
  locs ∩ r = ∅ ->
  valid_roots r σ ->
  valid_roots r (deallocate locs σ).
Proof.
  pattern locs. eapply set_ind_L; clear locs;
    unfold deallocate.
  { intros. rewrite gmap_mset_empty. eauto. }
  { intros ? ? ? IH ? ? ?.
    rewrite gmap_mset_snoc'; last set_solver.
    apply valid_roots_free. set_solver.
    apply IH; set_solver. }
Qed.

Lemma valid_roots_alloc r l bs σ :
  valid_roots r σ ->
  valid_roots (r ∪ {[l]}) (<[l:=BBlock bs]> σ).
Proof.
  intros Hr l' Hl'. simpl.
  apply elem_of_union in Hl'.
  split.
  { destruct Hl' as [Hl'|]; last set_solver.
    apply Hr in Hl'. set_solver. }
  destruct (decide (l=l')); subst.
  { by rewrite lookup_insert. }
  {  destruct Hl' as [Hl'|]; last set_solver.
     rewrite lookup_insert_ne; try easy.
     by apply Hr. }
Qed.

Lemma valid_roots_weak r1 r2 σ :
  r1 ⊆ r2 ->
  valid_roots r2 σ ->
  valid_roots r1 σ.
Proof.
  intros Hi Hr l Hl.
  assert (l ∈ r2) as Hl' by set_solver.
  by apply Hr in Hl'.
Qed.

(* LATER may be used in other lemmas *)
Lemma lookup_not_deallocated (l:loc) (s:store) :
  l ∈ dom s ->
  s !! l <> Some BDeallocated ->
  exists bs, s !! l = Some (BBlock bs).
Proof.
  intros.
  destruct (s!!l) eqn:E.
  2:{ by apply not_elem_of_dom in E. }
  destruct b; try easy.
  by eexists _.
Qed.

Lemma gc_read_root l bs r σ σ' :
  l ∈ r ->
  gc r σ σ' ->
  σ !! l = Some (BBlock bs) ->
  σ' !! l = Some (BBlock bs).
Proof.
  intros Hl [Hr1 Hr2] Hb.
  assert (l ∈ dom (to_rstore r σ)) as Hlr.
  { rewrite dom_to_rstore.
    apply elem_of_dom. rewrite Hb. easy. }
  apply Hr2 in Hlr.

  assert (reachable (to_rstore r σ) l) as Hlr'.
  { eauto using prove_reachable_root. }

  destruct Hlr as [Hlr|]; try easy.
  do 2 rewrite lookup_total_to_rstore in Hlr.
  do 2 rewrite lookup_total_alt in Hlr.
  rewrite Hb in Hlr. simpl in Hlr.
  destruct (σ' !! l).
  2:{ exfalso. by destruct (decide (l ∈ r)). }
  { unfold to_rblock in Hlr.
    destruct b; try (by destruct (decide (l ∈ r))).
    destruct (decide (l ∈ r)); try easy. injection Hlr.
    now intros ->. }
Qed.

Lemma gc_preserves_reachable σ r σ' l :
  closed σ ->
  gc r σ σ' ->
  reachable (to_rstore r σ') l ->
  reachable (to_rstore r σ) l.
Proof.
  intros ? [].
  apply store_evolution_preserves_reachable; try easy.
  apply closed_from_change with (r1:=∅). eauto.
Qed.

Lemma gc_read_root_inv l bs r σ σ' :
  closed σ ->
  l ∈ r ->
  gc r σ σ' ->
  σ' !! l = Some (BBlock bs) ->
  σ !! l = Some (BBlock bs).
Proof.
  intros ? Hl Hgc Hb. generalize Hgc. intros [Hr1 Hr2].
  assert (l ∈ dom (to_rstore r σ')) as Hlr.
  { rewrite dom_to_rstore.
    apply elem_of_dom. rewrite Hb. easy. }
  apply Hr1 in Hlr.
  apply Hr2 in Hlr.

  assert (reachable (to_rstore r σ) l).
  { eauto using gc_preserves_reachable, prove_reachable_root. }

  destruct Hlr as [Hlr|]; try easy.
  do 2 rewrite lookup_total_to_rstore in Hlr.
  do 2 rewrite lookup_total_alt in Hlr.
  rewrite Hb in Hlr. simpl in Hlr.
  destruct (σ !! l).
  2:{ exfalso. by destruct (decide (l ∈ r)). }
  { unfold to_rblock in Hlr.
    destruct b; try (by destruct (decide (l ∈ r))).
    destruct (decide (l ∈ r)); try easy. injection Hlr.
    now intros ->. }
Qed.

Lemma gc_preserves_valid_roots r σ1 σ2 :
  gc r σ1 σ2 ->
  valid_roots r σ1 ->
  valid_roots r σ2.
Proof.
  intros Hgc Hr l Hl. generalize Hl. intros Hl'.
  apply Hr in Hl. destruct Hl as (Hd&Hl).
  rewrite -(gc_dom Hgc).
  split; try easy.
  destruct (lookup_not_deallocated Hd Hl) as (bs,E).
  rewrite E in Hl.
  erewrite (gc_read_root Hl' Hgc).
  exact Hl. easy.
Qed.

Lemma successor_to_rstore r s l l' bs :
  s !! l = Some bs ->
  l' ∈ pointers bs <-> successor (to_rstore r s) l l'.
Proof.
  intros Hbs.
  rewrite /successors /successor /successors lookup_to_rstore Hbs.
  simpl. rewrite rblock_pointer_set_eq.
  easy.
Qed.

Lemma no_reachable_freed_weak r1 r2 σ :
  closed σ ->
  no_reachable_freed (to_rstore r2 σ) ->
  r1 ⊆ r2 ->
  no_reachable_freed (to_rstore r1 σ).
Proof.
  intros Hclo Hn Hi l Hl.
  assert (l ∈ dom σ).
  { rewrite -(dom_to_rstore r1).
    eapply closed_closed_from in Hclo.
    eauto using closed_reachable_in_dom. }
  eapply to_rstore_mono_reachable in Hl; eauto.
  apply Hn in Hl.
  rewrite lookup_to_rstore in Hl. rewrite lookup_to_rstore.
  destruct (σ !! l); try easy.
  simpl in *. unfold to_rblock in *.
  destruct (decide (l ∈ r2)); try easy;
    destruct b; try easy; by destruct (decide (l ∈ r1)).
Qed.

Record correct r (σ:store) :=
  { correct_closed : closed σ;
    correct_roots : valid_roots r σ;
    correct_dangl : no_reachable_freed (to_rstore r σ) }.

Lemma correct_init :
  correct ∅ ∅.
Proof.
  constructor;
    eauto using closed_init,
    valid_roots_init,no_reachable_freed_init.
Qed.

Lemma correct_weak r1 r2 σ :
  correct r2 σ ->
  r1 ⊆ r2 ->
  correct r1 σ.
Proof.
  intros [] ?.
  constructor; eauto using valid_roots_weak,no_reachable_freed_weak.
Qed.

Lemma successors_to_rstore r σ l :
  successors (to_rstore r σ) l = successors σ l.
Proof.
  unfold successors.
  rewrite map_lookup_imap.
  destruct (σ !! l); eauto. simpl.
  rewrite rblock_pointer_set_eq //.
Qed.

Lemma prove_not_reachable_group r locs σ :
  locs ⊆ dom σ ->
  locs ∩ r = ∅ ->
  (∀ m m' : loc, m' ∈ successors σ m → m' ∈ locs → m ∈ locs) ->
  forall l, l ∈ locs -> ¬ reachable (to_rstore r σ) l.
Proof.
  intros ? ? Hc.
  eapply prove_unreachable_region; eauto.
  { intros. intros E.
    apply is_root_to_rstore in E. destruct E.
    set_solver. }
  { intros ? ? ? Hr. eapply Hc; eauto.
    rewrite successors_to_rstore in Hr.
    eauto. }
Qed.

Lemma prove_not_reachable r l σ :
  l ∈ dom σ ->
  l ∉ r -> (* l not a root *)
  (∀ m, l ∈ successors σ m → m = l) -> (* l is its only succ. *)
  ¬ reachable (to_rstore r σ) l.
Proof.
  intros ? ? Hl.
  apply prove_not_reachable_group with (locs:={[l]} : gset loc).
  1,2,4:set_solver.
  intros ? l' E ?.
  assert (l' = l) by set_solver. subst.
  apply Hl in E. set_solver.
Qed.

Lemma gc_read_reachable l r σ σ' :
  closed σ ->
  gc r σ σ' ->
  reachable (to_rstore r σ) l ->
  σ' !! l = σ !! l.
Proof.
  intros Hclo Hgc Hl. generalize Hgc. intros [Hr1 Hr2].
  assert (l ∈ dom (to_rstore r σ)) as Hd.
  { eapply closed_closed_from in Hclo.
    eauto using closed_reachable_in_dom. }
  assert (l ∈ dom σ).
  { by rewrite -(dom_to_rstore r). }
  assert (l ∈ dom σ').
  { by rewrite -(dom_to_rstore r) -Hr1. }

  apply Hr2 in Hd. destruct Hd as [Hd|Hd]; try easy.
  do 2 rewrite lookup_total_alt lookup_to_rstore in Hd.

  destruct (σ !! l) eqn:E1, (σ' !! l) eqn:E2; simpl in *; try easy.
  { apply to_rblock_eq_inv in Hd. subst. easy. }
  { exfalso. by apply not_elem_of_dom in E2. }
  { exfalso. by apply not_elem_of_dom in E1. }
Qed.

Lemma gc_preserves_no_reachable_freed r σ σ' :
  closed σ ->
  gc r σ σ' ->
  no_reachable_freed (to_rstore r σ) ->
  no_reachable_freed (to_rstore r σ').
Proof.
  intros ? ? Hdang ? Hl. generalize Hl. intros ?.
  eapply (@gc_preserves_reachable σ) in Hl; try easy.
  apply Hdang in Hl.
  rewrite lookup_to_rstore in Hl. rewrite lookup_to_rstore.
  erewrite gc_read_reachable; eauto.
  eauto using gc_preserves_reachable.
Qed.

Lemma gc_free_group (r:gset loc) locs σ :
  locs ∩ r = ∅ ->
  locs ⊆ dom σ ->
  (∀ m m' : loc, m' ∈ successors σ m → m' ∈ locs → m ∈ locs) ->
  gc r σ (deallocate locs σ).
Proof.
  constructor.
  { do 2 rewrite dom_to_rstore. rewrite dom_gmap_mset. set_solver. }
  intros l'. rewrite dom_to_rstore. intros Hl'. simpl.
  destruct (decide (l' ∈ locs)); subst.
  { right. split.
    { eapply prove_not_reachable_group; eauto. }
    { rewrite lookup_total_to_rstore lookup_total_alt.
      rewrite gmap_lookup_mset_inside; eauto. } }
  left.
  do 2 rewrite lookup_total_to_rstore.
  do 2 rewrite lookup_total_alt.
  rewrite gmap_lookup_mset_outside; eauto.
Qed.

Lemma gc_free (r:gset loc) l σ :
  l ∉ r ->
  l ∈ dom σ ->
  (∀ m, l ∈ successors σ m → m = l) ->
  gc r σ (<[l:=BDeallocated]> σ).
Proof.
  intros Hl.
  constructor.
  { do 2 rewrite dom_to_rstore. simpl. rewrite dom_insert.
    set_solver. }
  intros l'. rewrite dom_to_rstore. intros Hl'. simpl.
  destruct (decide (l=l')); subst.
  { right.
    rewrite lookup_total_to_rstore lookup_total_insert.
    eauto using prove_not_reachable. }
  left.
  do 2 rewrite lookup_total_to_rstore.
  by rewrite lookup_total_insert_ne.
Qed.

Lemma free_group_preserves_no_reachable_freed (r:gset loc) locs σ :
  locs ∩ r = ∅ ->
  locs ⊆ dom σ ->
  (∀ m m' : loc, m' ∈ successors σ m → m' ∈ locs → m ∈ locs) ->
  closed σ ->
  no_reachable_freed (to_rstore r σ) ->
  no_reachable_freed (to_rstore r (deallocate locs σ)).
Proof.
  intros.
  assert (gc r σ (deallocate locs σ)) as Hgc.
  { eauto using gc_free_group. }
  eapply gc_preserves_no_reachable_freed in Hgc; eauto.
Qed.

Lemma free_group_preserves_closed locs σ :
  locs ⊆ dom σ ->
  closed σ ->
  closed (deallocate locs σ).
Proof.
  unfold closed, closed_from.
  pattern locs. eapply set_ind_L; clear locs;
    unfold deallocate.
  { intros. rewrite gmap_mset_empty. eauto. }
  { intros ? ? ? IH ? ?.
    rewrite gmap_mset_snoc'; last set_solver.
    rewrite to_rstore_insert.
    apply closed_insert_no_successors; last easy.
    apply IH; set_solver. }
Qed.

Lemma free_group_preserves_correct r locs σ :
  locs ⊆ dom σ ->
  locs ∩ r = ∅ ->
  (∀ m m' : loc, m' ∈ successors σ m → m' ∈ locs → m ∈ locs) ->
  correct r σ ->
  correct r (deallocate locs σ).
Proof.
  intros ? ? ? [].
  constructor;
    eauto using
    free_group_preserves_closed,
    valid_roots_free_group,
    free_group_preserves_no_reachable_freed.
Qed.

Lemma free_preserves_correct r l σ :
  l ∈ dom σ ->
  l ∉ r ->
  (∀ m, l ∈ successors σ m → m = l) ->
  correct r σ ->
  correct r (<[l:=BDeallocated]> σ).
Proof.
  intros ? ? Hm Hco.
  apply free_group_preserves_correct with (locs:={[l]} : gset loc) in Hco.
  { unfold deallocate in *. rewrite gmap_mset_singleton in Hco; eauto. }
  1,2:set_solver.
  intros. assert (m' = l) by set_solver. subst.
  set_solver.
Qed.

Lemma alloc_preserves_closed l n σ :
  σ !! l = None ->
  closed σ ->
  closed (<[l:=BBlock (replicate n val_unit)]> σ).
Proof.
  intros.
  destruct σ as [σ ?].
  unfold closed, closed_from. simpl.
  rewrite to_rstore_insert.
  apply closed_insert_no_successors; try easy. simpl.
  fold (to_rblock ∅ l (BBlock (replicate n val_unit))).
  now rewrite rblock_pointer_set_eq block_pointer_set_new_block.
Qed.

(* LATER can be used in other lemmas ? *)
Lemma reachable_to_rstore r s l :
  reachable (to_rstore r s) l
  <-> exists l', l' ∈ r /\ s !!! l' <> BDeallocated /\ rtc (successor (to_rstore ∅ s)) l' l.
Proof.
  split.
  { intros (l',(Hr&Hrtc)).
    exists l'. apply is_root_to_rstore in Hr.
    split; try split; try easy.
    eauto using rtc_successors_successor,to_rstore_preserves_successors. }
  { intros (l',(?&?&Hrtc)).
    exists l'.
    split.
    { by eapply is_root_to_rstore. }
    { eauto using rtc_successors_successor,to_rstore_preserves_successors. } }
Qed.

Lemma rtc_to_rstore_alloc x l l' n s :
  s !! l = None ->
  rtc (successor (to_rstore ∅ (<[l:=BBlock (replicate n val_unit)]> s))) x l' ->
  rtc (successor (to_rstore ∅ s)) x l'.
Proof.
  intros ?.
  induction 1; try easy.
  eapply rtc_l; last apply IHrtc.
  rewrite /successor /successors lookup_to_rstore in H0.
  destruct (decide (l=x)); subst.
  { rewrite lookup_insert in H0; simpl in *. (* LATER en commun avec en dessous *)
    destruct (decide (x ∈ ∅)); first set_solver.
    rewrite rblock_pointer_set_block block_pointer_set_new_block in H0.
    set_solver. }
  { rewrite lookup_insert_ne in H0; try easy.
    destruct (s!!x) eqn:E; simpl in *; last set_solver.
    rewrite /successor /successors lookup_to_rstore E //. }
Qed.

Lemma no_reachable_freed_alloc r l n σ :
  closed σ ->
  σ !! l = None ->
  no_reachable_freed (to_rstore r σ) ->
  no_reachable_freed
    (to_rstore (r ∪ {[l]}) ((<[l:=BBlock (replicate n val_unit)]> σ))).
Proof.
  intros Hclo Hl Hdang l' Hl'. simpl in *.
  rewrite lookup_to_rstore.
  destruct (decide (l=l')); subst.
  { rewrite lookup_insert. simpl. by (destruct (decide (l' ∈ r ∪ {[l']}))). }
  rewrite lookup_insert_ne; last easy.
  destruct (σ !! l') eqn:E; simpl; last easy.
  assert (reachable (to_rstore r σ) l') as Hreach.
  { apply reachable_to_rstore in Hl'. destruct Hl' as (x,(Hsucc&Hl'&Hrtc)).
    destruct (decide (l=x)); subst.
    { exfalso. inversion Hrtc; try easy; subst.
      rewrite /successor /successors lookup_to_rstore lookup_insert in H.
      simpl in H. destruct (decide (x ∈ ∅)); first set_solver.
      rewrite rblock_pointer_set_block block_pointer_set_new_block in H.
      set_solver. }
    apply reachable_to_rstore.
    rewrite lookup_total_insert_ne in Hl'; try easy.
    exists x. split; last split; try easy.
    { set_solver. }
    { eauto using rtc_to_rstore_alloc. } }
  apply Hdang in Hreach. rewrite lookup_to_rstore E in Hreach.
  simpl in *.  unfold to_rblock in *.
  destruct (decide (l' ∈ r)); destruct (decide (l' ∈ r ∪ {[l]}));
    try easy; set_solver.
Qed.

Lemma alloc_preserves_correct maxsize r l n σ :
  σ !! l = None ->
  n <= available maxsize σ ->
  correct r σ ->
  correct (r ∪ {[l]}) (<[l:=BBlock (replicate n val_unit)]> σ).
Proof.
  intros ? ? [? ? Hr].
  constructor.
  { eauto using alloc_preserves_closed. }
  { eapply valid_roots_weak.
    2:{ eauto using valid_roots_alloc. }
    set_solver. }
  { by eapply no_reachable_freed_alloc. }
Qed.

Lemma valid_roots_inline_block l bs r σ :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  correct r σ ->
  valid_roots (r ∪ locs bs) σ.
Proof.
  intros ? Hb [Hclo Hr Hdang] l' Hl'.
  apply elem_of_union in Hl'.
  destruct Hl' as [Hl'|Hl'].
  { apply Hr in Hl'. easy. }

  assert (reachable (to_rstore r σ) l') as Hreach.
  { exists l. split.
    { apply is_root_to_rstore. rewrite lookup_total_alt Hb //. }
    eapply rtc_l; last easy.
    rewrite -successor_to_rstore; last apply Hb.
    by rewrite -pointers_locs. }

  split.
  { rewrite -(dom_to_rstore r).
    apply closed_reachable_in_dom.
    { eapply closed_from_change, Hclo. }
    apply Hreach. }
  { eapply rno_reachable_freed.
    { eapply closed_from_change, Hclo. }
    { apply Hdang. }
    { apply Hreach. } }
Qed.

Lemma no_reachable_freed_inline_roots l bs r s :
  l ∈ r ->
  s !! l = Some (BBlock bs) ->
  no_reachable_freed (to_rstore r s) ->
  no_reachable_freed (to_rstore (r ∪ locs bs) s).
Proof.
  intros Hl Hsl Hdang l' Hl'.
  assert (reachable (to_rstore r s) l') as Hreach.
  { apply reachable_to_rstore in Hl'. destruct Hl' as (x,(Hr&?&Hrtc)).
    apply reachable_to_rstore.
    apply elem_of_union in Hr. destruct Hr.
    { exists x. easy. }
    { exists l. rewrite lookup_total_alt Hsl.
      split; last split; try easy.
      eapply rtc_l; last apply Hrtc.
      rewrite /successor /successors lookup_to_rstore Hsl. simpl.
      destruct ( decide (l ∈ ∅)); first set_solver.
      rewrite rblock_pointer_set_block.
      now apply pointers_locs. } }
  apply Hdang in Hreach.
  rewrite lookup_to_rstore in Hreach. rewrite lookup_to_rstore.
  destruct (s !! l') as [b|]; try easy. simpl.
  unfold to_rblock in *. simpl in *.
  destruct (decide (l' ∈ r ∪ locs bs)); destruct (decide (l' ∈ r));
    try easy; destruct b; try easy.
Qed.

Lemma correct_inline_root l bs r σ :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  correct r σ ->
  correct (r ∪ locs bs) σ.
Proof.
  intros Hl ? Hco. generalize Hco. intros [].
  constructor; try easy.
  { eauto using (valid_roots_inline_block Hl). }
  { eauto using (no_reachable_freed_inline_roots _ Hl). }
Qed.

Lemma valid_roots_udpate r l n v bs σ :
  valid_roots r σ ->
  valid_roots r (<[l:=BBlock (<[n:=v]> bs)]> σ).
Proof.
  intros Hr l' Hl'. simpl.
  apply Hr in Hl'. destruct Hl'.
  split.
  { rewrite dom_insert. set_solver. }
  destruct (decide (l = l')); subst.
  { by rewrite lookup_insert. }
  { by rewrite lookup_insert_ne. }
Qed.

(* LATER to use *)
Lemma successor_to_rstore' r s l l' :
  successor (to_rstore r s) l l' <->
  exists b, (s!!l) = Some b /\ l' ∈ block_pointer_set b.
Proof.
  rewrite /successors /successor /successors lookup_to_rstore.
  destruct (s!!l) eqn:E; last set_solver. simpl in *.
  rewrite rblock_pointer_set_eq.
  split. by eexists _.
  intros (?&(R&?)). injection R. by intros ->.
Qed.

Lemma to_rstore_insert_root r n v σ l bs :
  l ∈ r ->
  (to_rstore r (<[l:=BBlock (<[n:=v]> bs)]> σ)) =
    <[l:=RRoot (<[n:=v]> bs)]> (to_rstore r σ).
Proof.
  intros.
  unfold to_rstore. simpl. rewrite map_imap_insert.
  f_equal. unfold to_rblock.
  by destruct (decide (l ∈ r)).
Qed.

Lemma reachable_update r n v σ l l' bs :
  l ∈ r ->
  valid_roots r σ ->
  σ !! l = Some (BBlock bs) ->
  locs v ⊆ r ->
  reachable (to_rstore r (<[l:=BBlock (<[n:=v]> bs)]> σ)) l' ->
  reachable (to_rstore r σ) l'.
Proof.
  intros ? Hv Hs ? Hl'.
  assert (to_rstore r σ !! l = Some (RRoot bs)) as Hrl.
  { rewrite lookup_to_rstore Hs. simpl.
    by destruct (decide (l ∈ r)). }
  rewrite to_rstore_insert_root in Hl'; last easy.
  eapply analyze_reachable_after_heap_update in Hl'; try apply Hrl; try easy.
  intros x Hx ?.
  apply block_pointer_set_insert in Hx.
  destruct Hx; try easy.
  assert (x ∈ r) by set_solver.
  eauto using prove_reachable_valid_root.
Qed.

Lemma no_reachable_freed_update v r l n bs σ :
  l ∈ r ->
  valid_roots r σ ->
  σ !! l = Some (BBlock bs) ->
  locs v ⊆ r ->
  no_reachable_freed (to_rstore r σ) ->
  no_reachable_freed (to_rstore r (<[l:=BBlock (<[n:=v]> bs)]> σ)).
Proof.
  intros ? ? Hs ? Hdang l' Hl'.
  assert (reachable (to_rstore r σ) l') as Hreach.
  { eauto using reachable_update. }
  apply Hdang in Hreach.
  rewrite lookup_to_rstore in Hreach. rewrite lookup_to_rstore.
  destruct (decide (l=l')); subst; simpl.
  { rewrite lookup_insert. simpl. by destruct (decide (l' ∈ r)). }
  now rewrite lookup_insert_ne.
Qed.

Lemma update_preserves_correct r l n v w bs σ :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  bs !! n = Some w ->
  locs v ⊆ r ->
  correct r σ ->
  correct r (<[l:=BBlock (<[n:=v]> bs)]> σ).
Proof.
  intros ? Hl Hw ? [Hclo Hroot Hdang].
  unfold closed,valid_store in *.
  constructor.
  { unfold closed, closed_from. simpl.
    rewrite to_rstore_insert.
    apply closed_insert; try easy.
    rewrite rblock_pointers_eq (pointers_store w);
      try easy.
    intros l' Hl'.
    apply gmultiset_elem_of_disj_union in Hl'.
    destruct Hl'.
    { eapply Hclo. rewrite -successor_to_rstore; last apply Hl.
      multiset_solver. }
    rewrite dom_to_rstore.
    assert (l' ∈ r) as Hl' by (destruct v; set_solver).
    apply Hroot in Hl'.
    easy. }
  { eauto using valid_roots_udpate. }
  { now apply no_reachable_freed_update. }
Qed.

(* ------------------------------------------------------------------------ *)
(* GC basically preserves everything. *)

Lemma gc_preserves_valid_store maxsize r σ σ' :
  gc r σ σ' ->
  valid_store maxsize σ ->
  valid_store maxsize σ'.
Proof.
  unfold valid_store.
  intros Hgc. generalize Hgc. intros.
  intros. transitivity (size_heap σ); try easy.
  eauto using gc_non_size_increasing.
Qed.

Lemma gc_preserves_closed r σ σ' :
  gc r σ σ' ->
  closed σ ->
  closed σ'.
Proof.
  intros Hgc Hclo.
  eapply gc_weak with (r1:=∅) in Hgc; try easy.
  unfold closed, closed_from in *.
  eauto using store_evolution_preserves_closedness.
Qed.

Lemma gc_preserves_correct r σ σ' :
  gc r σ σ' ->
  correct r σ ->
  correct r σ'.
Proof.
  intros ? [].
  constructor;
    eauto using gc_preserves_valid_store, gc_preserves_closed, gc_preserves_valid_roots, gc_preserves_no_reachable_freed.
Qed.

Lemma gc_preserves_related r σ σ' θ :
  closed σ ->
  gc r σ σ' ->
  related r σ θ ->
  related r σ' θ.
Proof.
  unfold related, closed.
  intros Hclo. intros.
  apply closed_from_change with (r2:=r) in Hclo.
  eauto using store_evolution_preserves_store_agreement.
Qed.

(* ------------------------------------------------------------------------ *)
(* Free preserves related *)

Lemma to_rstore_deallocate r locs σ :
  locs ⊆ dom σ->
  to_rstore r (deallocate locs σ) = deallocate locs (to_rstore r σ).
Proof.
  pattern locs. eapply set_ind_L; clear locs;
    unfold deallocate.
  { intros. do 2 rewrite gmap_mset_empty. eauto. }
  { intros ? ? ? IH ?.
    rewrite gmap_mset_snoc'; last set_solver.
    rewrite to_rstore_insert.
    rewrite gmap_mset_snoc'.
    2:{ rewrite dom_to_rstore. set_solver. }
    simpl. f_equal. rewrite IH //. set_solver. }
Qed.

Lemma free_group_preserves_related r locs σ θ :
  locs ∩ r = ∅ ->
  locs ⊆ dom θ ->
  (∀ m m' : loc, m' ∈ successors θ m → m' ∈ locs → m ∈ locs) ->
  related r σ θ ->
  related r σ (deallocate locs θ).
Proof.
  intros E ? ? ?. unfold related in *.
  rewrite to_rstore_deallocate.
  apply store_agreement_deallocate; eauto.
  1,3:rewrite ?dom_to_rstore; set_solver.
  intros.
  eapply prove_not_reachable_group; eauto.
Qed.

Lemma free_preserves_related r l σ θ :
  l ∈ dom θ -> (* l is in the store *)
  l ∉ r -> (* l not a root *)
  (∀ m, l ∈ successors θ m → m = l) -> (* l is its only succ. *)
  related r σ θ ->
  related r σ (<[l:=BDeallocated]> θ).
Proof.
  intros E ? ? ?. unfold related in *.
  rewrite to_rstore_insert. simpl.
  assert (RDeallocated = deallocated) as -> by easy.
  eapply store_agreement_free; try easy.
  { rewrite dom_to_rstore //. }
  { eauto using prove_not_reachable. }
Qed.

Lemma alloc_preserves_related n l r σ θ :
  related r σ θ ->
  σ !! l = None ->
  θ !! l = None ->
  related (r ∪ {[l]})
          (<[l:=BBlock (replicate n val_unit)]> σ)
          (<[l:=BBlock (replicate n val_unit)]> θ).
Proof.
  intros Ha Hl1 Hl2. unfold related in *.
  do 2 rewrite to_rstore_insert.
  rewrite to_rblock_in; last set_solver.
  do 2 (rewrite to_rstore_not_in; last easy).

  apply store_agreement_alloc_cell; try easy.
  { rewrite lookup_to_rstore.
    rewrite Hl1.
    easy. }
  { intros x Hx. exfalso. simpl in Hx.
    rewrite rblock_pointer_set_root in Hx.
    rewrite block_pointer_set_new_block in Hx.
    set_solver. }
Qed.

Lemma reachable_inline_root l l' r bs σ :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  reachable (to_rstore (r ∪ locs bs) σ) l' ->
  reachable (to_rstore r σ) l'.
Proof.
  intros Hl Hb (root,(Hroot&Hrtc)).
  apply is_root_to_rstore in Hroot.
  destruct Hroot as (Hro1, Hro2).
  apply elem_of_union in Hro1.
  destruct Hro1.
  { exists root. split.
    { apply is_root_to_rstore. easy. }
    { eapply rtc_successors_successor; try apply Hrtc.
      intros. by erewrite to_rstore_preserves_successors. } }
  { exists l. split.
    { apply is_root_to_rstore.
      rewrite lookup_total_alt. rewrite Hb.
      easy. }
    { eapply rtc_l; last first.
      { eapply rtc_successors_successor; try apply Hrtc.
        intros. by erewrite to_rstore_preserves_successors. }
      unfold successor, successors.
      rewrite lookup_to_rstore. rewrite Hb. simpl.
      destruct (decide (l ∈ r)); try easy.
      rewrite rblock_pointer_set_root.
      by rewrite block_pointer_set_block_elem. } }
Qed.

Lemma related_inline_block_root l bs r σ θ :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  related r σ θ ->
  related (r ∪ locs bs) σ θ.
Proof.
  intros Hl Hb Hag. generalize Hag. intros [Hd _].
  constructor; try easy.
  { do 2 rewrite dom_to_rstore in Hd.
    by do 2 rewrite dom_to_rstore. }
  split.
  { intros l'.
    split; intros Hl'.
    { eapply to_rstore_mono_reachable;
        last eapply (store_agreement_preserves_reachable _ _ _ Hag).
      { set_solver. }
      apply (reachable_inline_root _ Hl Hb Hl'). }
    { eapply to_rstore_mono_reachable;
        last eapply (store_agreement_preserves_reachable _ _ _ Hag).
      { set_solver. }
      assert (θ !! l = Some (BBlock bs)) as Hb'.
      { apply store_agreement_symmetric in Hag.
        by rewrite (related_read_root _ Hag Hb). }
      apply (reachable_inline_root _ Hl Hb' Hl'). } }
  { intros l' Hl'.
    apply (reachable_inline_root _ Hl Hb) in Hl'.
    do 2 rewrite lookup_total_to_rstore.
    do 2 rewrite lookup_total_alt.

    apply store_agreement_symmetric in Hag.
    eapply store_agreement_preserves_reachable in Hl'.
    2:{ apply Hag. }
    do 2 f_equal.
    do 2 rewrite dom_to_rstore in Hd.
    destruct ((σ !! l')) as [b|] eqn:E.
    { by rewrite (related_read_reachable _ Hag E). }
    { symmetry. apply not_elem_of_dom. rewrite <- Hd. by apply not_elem_of_dom. } }
Qed.

(* see related_heap_update *)
Lemma update_preserves_related r n l v w vs σ θ :
  l ∈ r ->
  locs v ⊆ r ->
  correct r σ -> (* for valid_roots. *)
  vs !! n = Some w ->
  σ !! l = Some (BBlock vs) ->
  related r σ θ ->
  related r (<[l:=BBlock (<[n:=v]> vs)]> σ)
          (<[l:=BBlock (<[n:=v]> vs)]> θ).
Proof.
  intros ? Hlv Hco Hw Hl [].
  unfold related.
  do 2 rewrite to_rstore_insert.
  eapply store_agreement_cell_update; try easy.
  { rewrite lookup_to_rstore Hl //. }
  1,2:simpl; by (destruct (decide (l ∈ r))).

  intros l' Hl'.
  rewrite rblock_pointers_eq in Hl'.
  rewrite (pointers_store _ _ _ _ Hw) in Hl'.
  apply gmultiset_elem_of_disj_union in Hl'.
  destruct Hl' as [Hl'|Hl'].
  (* l' was from the original block *)
  { apply reachable_snoc with l.
    { eauto using prove_reachable_root. }
    apply (successor_to_rstore _ _ _ _ Hl).
    multiset_solver. }
  (* l' is new *)
  { assert (l' ∈ r).
    { rewrite /val_pointer_multiset in Hl'.
      destruct v; set_solver. }
    destruct Hco.
    by apply prove_reachable_valid_root. }
Qed.

(* ------------------------------------------------------------------------ *)
(* GC has the diamond property. *)

Lemma gc_diamond r σ1 σ2 σ3 :
  closed σ1 ->
  gc r σ1 σ2 ->
  gc r σ1 σ3 ->
  exists σ4, gc r σ2 σ4 /\ gc r σ3 σ4.
Proof.
  intros Hclo ? ?.
  apply closed_from_change with (r2:=r) in Hclo.
  exists (rcollect r σ1).
  unfold gc in *. rewrite to_rstore_rcollect.
  split; now apply store_evolution_collect_strong.
Qed.
