From stdpp Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.
From spacelambda.spacelang Require Import stdpp gset_fixpoint rhypotheses.

(* This file contains mathematical results about the notions of successor,
   reachability, garbage collection, agreement between the physical store
   and the conceptual store, etc. *)

(* ------------------------------------------------------------------------ *)

Section Successors.

(* We expect a countable type [L] of locations and an inhabited type [B]
   of blocks. *)

Context `{ RHypotheses L B }.

(* ------------------------------------------------------------------------ *)

(* Basic definitions. *)

(* A store [s] is a finite map of locations to blocks. *)

Implicit Types s : gmap L B.

(* We write [locs] for a set of locations. *)

Implicit Types locs : gset L.

Notation dom := (dom (gset L)).

(* With respect to the store [s], there is an edge of [l] to [l'] iff [l']
   is a successor of [l]. *)

Definition successor s l l' :=
  l' ∈ successors s l.

(* ------------------------------------------------------------------------ *)

(* Reachability. *)

(* A memory location [r] is regarded as a root if it is the address of
   a stack cell. *)

Definition is_root s r :=
  ∃ b,
  s !! r = Some b ∧ is_stack_cell b.

Local Hint Unfold is_root : core.

(* An address [l] is reachable if and only there is a path from some
   root to [l]. *)

Definition reachable s l :=
  ∃ r, is_root s r ∧ rtc (successor s) r l.

(* The physical store and the conceptual stores are closed under successors.
   The physical store has no dangling pointers. The conceptual store can have
   dangling pointers, which means that a block can contain a deallocated
   location [l']; nevertheless, [l'] is still in the domain of the store. *)

Definition closed s :=
  ∀ l l',
  successor s l l' →
  l' ∈ dom s.

(* ------------------------------------------------------------------------ *)

(* Decidability of reachability. *)

(* In order to prove decidability of reachability, we build the reachability
   finite decidable set by iterating the function [add_successors] enough
   times on [roots] *)

Definition add_successors s (X : gset L) : gset L :=
  X ∪ ⋃ (map (fun l => dom (successors s l)) (elements X)).

Lemma add_successors_spec s X y :
  y ∈ add_successors s X <-> y ∈ X \/ exists x, x ∈ X /\ successor s x y.
Proof.
  rewrite elem_of_union.
  apply or_iff_compat_l.
  rewrite elem_of_union_list.
  split.
  - intros (Y & HY & Yy).
    apply elem_of_list_In, in_map_iff in HY.
    destruct HY as (x & <- & xX).
    exists x; split.
    + now apply elem_of_elements, elem_of_list_In.
    + now apply gmultiset_elem_of_dom.
  - intros (x & xX & xy).
    exists (dom (successors s x)); split.
    + rewrite elem_of_list_In in_map_iff.
      exists x; split; auto.
      now apply elem_of_list_In, elem_of_elements.
    + now apply gmultiset_elem_of_dom.
Qed.

Instance decision_is_root s l : Decision (is_root s l).
Proof.
  unfold is_root. destruct (s !! l) as [ b | ].
  - destruct (decision_is_stack_cell b).
    + left; eauto.
    + right; intros (b' & [[= <-] ?]). tauto.
  - right; intros (b & [[=] ?]).
Qed.

Definition roots s : gset L := filter (is_root s) (dom s).

Lemma roots_spec s x : is_root s x <-> x ∈ roots s.
Proof.
  unfold roots.
  rewrite elem_of_filter.
  cut (is_root s x -> x ∈ dom s); [ intuition | ].
  intros (r & Hr & _).
  eapply prove_in_dom; eauto.
Qed.

(* We use the fixed point construction from our [gset_fixpoint], for which we
   require a upper bound on the iterated function and the starting set. We use
   the successors of the domain of [s] as our bound *)

Lemma roots_bounded s : roots s ⊆ add_successors s (dom s).
Proof.
  intros x Hx.
  apply roots_spec in Hx.
  unfold add_successors.
  apply elem_of_union_l.
  destruct Hx as (r & Hr & _).
  eapply prove_in_dom; eauto.
Qed.

Lemma add_successors_bounded s X :
  X ⊆ add_successors s (dom s) ->
  add_successors s X ⊆ add_successors s (dom s).
Proof.
  intros HX y.
  rewrite !add_successors_spec.
  intros [ | (x & Hx & xy) ].
  - rewrite <-add_successors_spec. now apply HX.
  - pose proof xy as xy'.
    unfold successor, successors in xy.
    destruct (s !! x) eqn:E.
    + right; exists x; split; auto.
      eapply prove_in_dom; eauto.
    + inversion xy.
Qed.

(* We can now define the finite set of reachable locations *)

Definition reachable_gset s : gset L :=
  gset_fixpoint
    (add_successors s)         (* iterated function *)
    (roots s)                  (* starting set *)
    (add_successors s (dom s)) (* bound *).

(* The correspondance between [reachable] and [reachable_gset] is an induction
   on the reflexivity transitive closure of [successor] in one direction, and
   the induction principle for [gset_fixpoint] in the other direction *)

Lemma roots_reachable s :
  roots s ⊆ reachable_gset s.
Proof.
  eapply gset_fixpoint_upper with (n := 0).
  - intro. unfold add_successors. apply union_subseteq_l.
  - eapply roots_bounded.
  - intros; now apply add_successors_bounded.
Qed.

Lemma succ_reachable s x y :
  successor s x y ->
  x ∈ reachable_gset s ->
  y ∈ reachable_gset s.
Proof.
  intros xy Hx.
  unfold reachable_gset.
  erewrite <-(gset_fixpoint_limit _ _ _).
  - apply add_successors_spec. right. eauto.
  - intro. unfold add_successors. apply union_subseteq_l.
  - eapply roots_bounded.
  - intros; now apply add_successors_bounded.
Qed.

Lemma rtc_succ_reachable s x y :
  rtc (successor s) x y ->
  x ∈ reachable_gset s ->
  y ∈ reachable_gset s.
Proof.
  intros T Hl.
  eapply (rtc_ind_r (fun x => x ∈ reachable_gset s)); eauto.
  intros; eapply succ_reachable; eauto.
Qed.

Lemma reachable_gset_spec s l : reachable s l <-> l ∈ reachable_gset s.
Proof.
  split.
  - intros (r & Hr & S).
    eapply rtc_succ_reachable; eauto.
    eapply roots_reachable; eauto.
    now apply roots_spec.
  - eapply gset_fixpoint_ind.
    + intro. unfold add_successors. apply union_subseteq_l.
    + eapply roots_bounded.
    + intros; now apply add_successors_bounded.
    + intros r Hr. exists r. repeat constructor. apply roots_spec, Hr.
    + intros X IH e He.
      apply add_successors_spec in He.
      destruct He as [He | (x & Hx & xe)]; auto.
      destruct (IH x Hx) as (y & Hy & yx).
      exists y. eauto with rtc.
Qed.

(* Thanks to its characterization via decidable sets, reachability is
   decidable *)

Global Instance decision_reachable s l :
  Decision (reachable s l).
Proof.
  destruct (decide (l ∈ reachable_gset s)); [ left | right ];
    now rewrite reachable_gset_spec.
Qed.

(* ------------------------------------------------------------------------ *)

(* Garbage collection. *)

(* The store contains both the shared heap and the stack cells allocated by
   every thread. These stack cells form the roots. Thus, all of the
   information that is needed to perform garbage collection is present in
   the store. In other words, it is possible to view garbage collection as
   a relation [store_evolution] of type [store → store → Prop]. *)

(* The evolution of a memory block under the action of the GC is to possibly
   be replaced with a deallocated block. However, this is permitted only if
   this block is unreachable. The GC is nondeterministic: we do not require
   that every unreachable block be immediately deallocated. *)

(* Because a stack cell is a root, it is reachable, therefore cannot be
   deallocated by the GC. *)

Definition block_evolution unreachable b1 b2 :=
  b1 = b2 ∨
  unreachable ∧ b2 = deallocated.

(* The evolution of the store under the action of the GC is the pointwise
   extension of the relation that describes the evolution of a block. *)

Definition store_evolution s1 s2 :=
  dom s1 ≡ dom s2 ∧
  ∀ l, l ∈ dom s1 →
  let unreachable := ¬ reachable s1 l in
  block_evolution unreachable (s1 !!! l) (s2 !!! l).

(* Whereas garbage collection is a relation (that is, it is nondeterministic),
   full garbage collection (which collects every unreachable block) is a
   function. *)

Definition collect_block s l b : option B :=
  Some (if decide (reachable s l) then b else deallocated).

Definition collect s : gmap L B :=
  map_imap (collect_block s) s.

(* ------------------------------------------------------------------------ *)

(* Agreement between the physical store and the conceptual store. *)

(* The two stores are related as follows: they agree on which blocks are
   reachable, and they agree on the content of every reachable block. *)

(* At unreachable memory locations, they can disagree in arbitrary ways:
   a location can be disallocated in reality and still allocated in the
   conceptual store; conversely, it can be deallocated in the conceptual
   store and not yet collected by the GC. *)

Definition store_agreement s1 s2 :=
  dom s1 ≡ dom s2 ∧
  (∀l, reachable s1 l <-> reachable s2 l) ∧
  (∀l, reachable s1 l → s1 !!! l = s2 !!! l).

(* ------------------------------------------------------------------------ *)

(* Miscellaneous little lemmas. *)

Lemma alloc_subseteq s l b :
  s !! l = None →
  s ⊆ <[l := b]> s.
Proof.
  intros. eapply insert_subseteq. eauto.
Qed.

Local Hint Resolve alloc_subseteq : core.

Lemma in_dom_insert l b s :
  l ∈ dom (<[l:=b]> s).
Proof.
  rewrite dom_insert. set_solver.
Qed.

Lemma in_dom_insert_otherwise l m b s :
  l ∈ dom s →
  l ∈ dom (<[m := b]> s).
Proof.
  rewrite dom_insert. set_solver.
Qed.

Local Hint Resolve in_dom_insert in_dom_insert_otherwise : in_dom closed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [successors] and [successor]. *)

Lemma prove_successor s l b l' :
  s !! l = Some b →
  l' ∈ pointers b →
  successor s l l'.
Proof.
  intros Hl ?. rewrite /successor /successors Hl //.
Qed.

Lemma successors_insert s l b :
  successors (<[l:=b]> s) l = pointers b.
Proof.
  rewrite /successors lookup_insert //.
Qed.

Lemma successors_insert_ne s l b l' :
  l ≠ l' →
  successors (<[l:=b]> s) l' = successors s l'.
Proof.
  intros. rewrite /successors lookup_insert_ne //.
Qed.

Lemma successor_insert s l b l' :
  successor (<[l:=b]> s) l l' <-> l' ∈ pointers b.
Proof.
  rewrite /successor successors_insert //.
Qed.

Lemma successor_insert_ne s l b l1 l2 :
  l ≠ l1 →
  successor (<[l:=b]> s) l1 l2 <-> successor s l1 l2.
Proof.
  intros. unfold successor. rewrite successors_insert_ne //.
Qed.

Lemma successor_deallocate_outside s locs l1 l2 :
  l1 ∉ locs →
  successor (deallocate locs s) l1 l2 <-> successor s l1 l2.
Proof.
  intros. unfold successor. rewrite successors_deallocate_outside //.
Qed.

Lemma successor_deallocate_implication s locs l1 l2 :
  successor (deallocate locs s) l1 l2 →
  successor s l1 l2.
Proof.
  pose proof (successors_deallocate_implication locs s l1).
  rewrite /successor. eauto using gmultiset_elem_of_subseteq.
Qed.

Lemma same_successors s s' l :
  dom s ≡ dom s' →
  l ∈ dom s →
  s !!! l = s' !!! l →
  successors s l = successors s' l.
Proof.
  intros Hdom Hl Heq. unfold successors.
  assert (l ∈ dom s') by eauto with in_dom.
  rewrite !lookup_lookup_total_dom //.
  rewrite Heq //.
Qed.

Lemma same_successor s s' l l' :
  dom s ≡ dom s' →
  l ∈ dom s →
  s !!! l = s' !!! l →
  successor s l l' <-> successor s' l l'.
Proof.
  intros. unfold successor. rewrite (same_successors s s' l) //.
Qed.

Lemma successor_monotonic s1 s2 l l' :
  s1 ⊆ s2 →
  successor s1 l l' →
  successor s2 l l'.
Proof.
  intros Hsub. rewrite /successor /successors.
  case_eq (s1 !! l); [ intros b Hl1 | intros; set_solver ].
  assert (Hl2: s2 !! l = Some b) by (eapply map_subseteq_spec; eauto).
  rewrite Hl2 //.
Qed.

Lemma rtc_successors_monotonic s1 s2 l l' :
  s1 ⊆ s2 →
  rtc (successor s1) l l' →
  rtc (successor s2) l l'.
Proof.
  induction 2; eauto using successor_monotonic with rtc.
Qed.

Lemma successor_already r s s' l' :
  s ⊆ s' →
  r ∈ dom s →
  successor s' r l' →
  successor s r l'.
Proof.
  intros Hsub Hr. unfold successor, successors.
  rewrite -> !lookup_lookup_total_dom by eauto with in_dom.
  erewrite <- gmap_lookup_total_subseteq by eauto.
  eauto.
Qed.

Lemma successor_in_dom s l l' :
  successor s l l' →
  l ∈ dom s.
Proof.
  rewrite /successor /successors.
  rewrite elem_of_dom.
  destruct (s !! l).
  + eauto.
  + set_solver.
Qed.

Local Hint Resolve successor_in_dom : in_dom.

Lemma nonexistent_successor s l l' :
  s !! l = None →
  successor s l l' →
  False.
Proof.
  rewrite /successor /successors. intros ->. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [is_root]. *)

Lemma is_root_monotonic s1 s2 r :
  s1 ⊆ s2 →
  is_root s1 r →
  is_root s2 r.
Proof.
  intros ? (b & ? & ?). exists b. split; [| eauto ].
  eapply map_subseteq_spec; eauto.
Qed.

Lemma is_not_root_monotonic s1 s2 r :
  s1 ⊆ s2 →
  r ∈ dom s1 →
  ¬ is_root s1 r →
  ¬ is_root s2 r.
Proof.
  intros Hsub Hdom Hnroot (b & ? & ?).
  eapply Hnroot. exists b. split; [| eauto ].
  (* We are proving a converse of [map_subseteq_spec]. *)
  rewrite -> elem_of_dom in Hdom.
  destruct Hdom as (b1 & Hs1r).
  rewrite -> map_subseteq_spec in Hsub.
  specialize (Hsub _ _ Hs1r).
  simplify_eq. eauto.
Qed.

Lemma is_root_insert b s r :
  is_root (<[r:=b]> s) r <->
  is_stack_cell b.
Proof.
  rewrite /is_root lookup_insert. split.
  - intros (? & ? & ?). simplify_eq. eauto.
  - eauto.
Qed.

Lemma is_root_insert_ne l b s r :
  l ≠ r →
  is_root (<[l:=b]> s) r <->
  is_root s r.
Proof.
  intro. rewrite /is_root lookup_insert_ne //.
Qed.

Lemma is_root_insert_1 b s r :
  is_stack_cell b →
  is_root (<[r:=b]> s) r.
Proof.
  rewrite is_root_insert //.
Qed.

Lemma is_root_insert_ne_1 l b s r :
  l ≠ r →
  is_root s r →
  is_root (<[l:=b]> s) r.
Proof.
  intros. rewrite is_root_insert_ne //.
Qed.

Lemma is_root_insert_ne_2 l b s r :
  l ≠ r →
  is_root (<[l:=b]> s) r →
  is_root s r.
Proof.
  intros. rewrite -is_root_insert_ne //.
Qed.

Local Hint Resolve
   is_root_insert_1 is_root_insert_ne_1 is_root_insert_ne_2
: core.

Lemma is_root_deallocated s r :
  ¬ is_root (<[r:=deallocated]> s) r.
Proof.
  intros (b & Hroot & ?).
  rewrite lookup_insert in Hroot.
  simplify_eq.
  eauto using stack_cell_not_deallocated.
Qed.

Lemma is_root_deallocate locs s r :
  is_root (deallocate locs s) r ↔
  is_root s r ∧ r ∉ locs.
Proof.
  rewrite /is_root /deallocate. split.
  - intros (b & Hroot & ?).
    rewrite -> gmap_lookup_mset_Some in Hroot.
    destruct Hroot as [ (Hr & ?) | (Hr & ?) ].
    + eauto.
    + subst. exfalso. eauto using stack_cell_not_deallocated.
  - intros ((b & Hroot & ?) & ?).
    rewrite gmap_lookup_mset_outside //.
    eauto.
Qed.

Lemma lookup_Some_in_dom s l b :
  s !! l = Some b →
  l ∈ dom s.
Proof.
  intros. rewrite elem_of_dom. eauto.
Qed.

Local Hint Resolve lookup_Some_in_dom : in_dom.

Lemma is_root_in_dom s r :
  is_root s r →
  r ∈ dom s.
Proof.
  intros (b & ? & ?). eauto with in_dom.
Qed.

Local Hint Resolve is_root_in_dom : in_dom.

Lemma closed_rtc_in_dom s l l' :
  closed s →
  rtc (successor s) l l' →
  l ∈ dom s → l' ∈ dom s.
Proof.
  induction 2; eauto.
Qed.

Local Hint Resolve closed_rtc_in_dom : in_dom.

Lemma is_root_reformulation s r :
  is_root s r <-> is_stack_cell (s !!! r).
Proof.
  case_eq (s !! r).
  { intros b Hr.
    rewrite /is_root Hr.
    rewrite lookup_total_alt Hr. simpl.
    split.
    - intros (? & ? & ?). simplify_eq. eauto.
    - eauto. }
  { intros Hr.
    rewrite /is_root Hr.
    rewrite lookup_total_alt Hr. simpl.
    split.
    - intros (? & ? & ?). simplify_eq.
    - pose proof inhabitant_not_stack_cell. tauto. }
Qed.

(* ------------------------------------------------------------------------ *)

(* A heap edge is an edge that does not lead to a stack cell. *)

Definition heap_edge s l l' :=
  successor s l l' ∧ ¬ is_root s l'.

Local Hint Unfold heap_edge : core.

(* A heap path is a path composed of heap edges. *)

(* A heap edge is (in particular) a successor edge. *)

Lemma heap_edge_implies_successor s l l' :
  heap_edge s l l' →
  successor s l l'.
Proof.
  destruct 1. eauto.
Qed.

Local Hint Resolve heap_edge_implies_successor : core.

Lemma prove_heap_edge_insert_eq c cell s l :
  l ∈ pointers cell →
  is_root s c →
  ¬ is_root s l →
  heap_edge (<[c:=cell]> s) c l.
Proof.
  constructor.
  + rewrite successor_insert //.
  + assert (l ≠ c) by (intros ->; tauto).
    eauto.
Qed.

Local Hint Resolve prove_heap_edge_insert_eq : core.

Lemma heap_path_implies_path s l l' :
  rtc (heap_edge s) l l' →
  rtc (successor s) l l'.
Proof.
  eauto using rtc_subrel.
Qed.

Local Hint Resolve heap_path_implies_path : core.

Lemma closed_heap_path_in_dom s l l' :
  closed s →
  rtc (heap_edge s) l l' →
  l ∈ dom s → l' ∈ dom s.
Proof.
  induction 2; eauto.
Qed.

Local Hint Resolve closed_heap_path_in_dom : in_dom.

(* If there is a path from some root to [l], then there is also a heap path
   from some root to [l]. The intuition is to keep only the last part of the
   path, from the last root that is encountered along the way to [l]. *)

Lemma existence_of_heap_path_preliminary s l l' :
  rtc (successor s) l l' →
  ∀ r,
  is_root s r →
  rtc (heap_edge s) r l →
  ∃ r,
  is_root s r ∧
  rtc (heap_edge s) r l'.
Proof.
  induction 1 as [| l m l' Hedge ? ? ]; [ eauto | intros ].
  assert (Decision (is_root s m)) by eauto using decision_is_root.
  case (decide (is_root s m)); eauto with rtc.
Qed.

Lemma existence_of_heap_path s r l :
  is_root s r →
  rtc (successor s) r l →
  ∃ r,
  is_root s r ∧ rtc (heap_edge s) r l.
Proof.
  eauto using existence_of_heap_path_preliminary with rtc.
Qed.

(* A memory location [l] is reachable (via an arbitrary path) if and
   only if it is reachable via a heap path. This gives us a tight
   characterization of reachability that can be useful when reasoning
   about updates to stack cells. *)

Lemma reachable_via_heap_path s l :
  reachable s l <->
  ∃ r, is_root s r ∧ rtc (heap_edge s) r l.
Proof.
  split; intros (r & ? & ?).
  - eauto using existence_of_heap_path.
  - exists r. eauto using rtc_subrel.
Qed.

Lemma heap_edge_already r s s' l' :
  s ⊆ s' →
  r ∈ dom s →
  heap_edge s' r l' →
  heap_edge s r l'.
Proof.
  intros ? ? (? & ?). split; eauto using successor_already, is_root_monotonic.
Qed.

Lemma heap_edge_monotonic s1 s2 l l' :
  s1 ⊆ s2 →
  closed s1 →
  heap_edge s1 l l' →
  heap_edge s2 l l'.
Proof.
  intros ? ? (? & ?).
  split; eauto using successor_monotonic, is_not_root_monotonic.
Qed.

Lemma heap_path_monotonic s1 s2 l l' :
  s1 ⊆ s2 →
  closed s1 →
  rtc (heap_edge s1) l l' →
  rtc (heap_edge s2) l l'.
Proof.
  induction 3; eauto using heap_edge_monotonic with rtc.
Qed.

(* A heap edge whose source is not [c] is preserved by an update to [c]. *)

Lemma heap_edge_cell_update c cell s l l' :
  is_root s c →
  is_root (<[c:=cell]> s) c →
  l ≠ c →
  heap_edge (<[c:=cell]> s) l l' <->
  heap_edge s l l'.
Proof.
  intros ? ?. rewrite /heap_edge. split; intros (Hsucc & Hnroot).
  + rewrite -> successor_insert_ne in Hsucc by eauto.
    assert (c ≠ l') by (intros ->; tauto).
    rewrite -> is_root_insert_ne in Hnroot by eauto.
    eauto.
  + rewrite -> successor_insert_ne by eauto.
    assert (c ≠ l') by (intros ->; tauto).
    rewrite -> is_root_insert_ne by eauto.
    eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [reachable]. *)

Lemma reachable_monotonic s1 s2 l :
  s1 ⊆ s2 →
  reachable s1 l →
  reachable s2 l.
Proof.
  rewrite /reachable. intros ? (r & ? & ?).
  eauto using is_root_monotonic, rtc_successors_monotonic.
Qed.

Lemma reachable_snoc s l l' :
  reachable s l →
  successor s l l' →
  reachable s l'.
Proof.
  intros (r & ? & ?) ?. exists r. eauto with rtc.
Qed.

Local Hint Resolve reachable_snoc : reachable.

Lemma reachable_path s l l' :
  rtc (successor s) l l' →
  reachable s l →
  reachable s l'.
Proof.
  induction 1; eauto with reachable.
Qed.

Local Hint Resolve reachable_path : reachable.

Lemma reachable_heap_path s l l' :
  rtc (heap_edge s) l l' →
  reachable s l →
  reachable s l'.
Proof.
  induction 1; eauto with reachable.
Qed.

Local Hint Resolve reachable_heap_path : reachable.

Lemma roots_are_reachable s r :
  is_root s r →
  reachable s r.
Proof.
  intros. exists r. eauto with rtc.
Qed.

Local Hint Resolve roots_are_reachable : reachable.

Lemma rtc_implies_reachable s r l :
  rtc (successor s) r l →
  is_root s r →
  reachable s l.
Proof.
  rewrite /reachable. eauto.
Qed.

Local Hint Resolve rtc_implies_reachable : reachable.

(* If two stores [s1] and [s2] have the same domain and agree on the content
   of the blocks that are reachable in [s1], then every block that is
   reachable in [s1] is also reachable in [s2]. *)

Lemma prove_reachable_implication s1 s2 :
  dom s1 ≡ dom s2 →
  (∀ l, l ∈ dom s1 -> reachable s1 l → s1 !!! l = s2 !!! l) →
  ∀ l, reachable s1 l → reachable s2 l.
Proof.
  intros ? Hag l (r & Hroot1 & Hpath).
  assert (Hreach1: reachable s1 r) by eauto with reachable.
  assert (Hroot2: is_root s2 r).
  { assert (r ∈ dom s1) by (now apply is_root_in_dom).
    revert Hroot1. rewrite !is_root_reformulation Hag //. }
  assert (Hreach2: reachable s2 r) by eauto with reachable.
  clear Hroot1 Hroot2. revert Hreach1 Hreach2.
  induction Hpath as [ r | r r' l Hedge1 _ IH ]; [ eauto |]. intros.
  assert (Hedge2: successor s2 r r')
    by (rewrite -same_successor; eauto with in_dom).
  eauto with reachable.
Qed.

(* If two stores [s1] and [s2] have the same domain and agree on the content
   of the blocks that are reachable in [s1] or [s2], then they have the same
   reachable blocks. *)

Lemma prove_reachable_coincidence s1 s2 :
  dom s1 ≡ dom s2 →
  (∀ l, reachable s1 l → s1 !!! l = s2 !!! l) →
  (∀ l, reachable s2 l → s1 !!! l = s2 !!! l) →
  ∀ l, reachable s1 l ↔ reachable s2 l.
Proof.
  intros.
  assert (dom s2 ≡ dom s1) by eauto.
  split; eauto using prove_reachable_implication, eq_sym.
Qed.

(* If [l'] is reachable from some root [r], and if [l] is not reachable
   from this root, then deallocating [l] does not compromise the fact
   that [l'] is reachable. *)

Lemma rtc_successor_free_direct r s l l' b :
  rtc (successor s) r l' →
  ¬ rtc (successor s) r l →
  rtc (successor (<[l:=b]> s)) r l'.
Proof.
  induction 1 as [| r ? l' Hsucc Hrtc IH ]; econstructor.
  - case (decide (r = l)); intro.
    { exfalso. subst l. eauto with rtc. }
    { rewrite /successor successors_insert_ne //. }
  - eauto with rtc.
Qed.

(* The reciprocal storement. *)

Lemma rtc_successor_free_reverse r s l l' b :
  rtc (successor (<[l:=b]> s)) r l' →
  ¬ rtc (successor s) r l →
  rtc (successor s) r l'.
Proof.
  induction 1 as [| r k l' Hsucc Hrtc IH ]; intros; eauto with rtc.
  assert (successor s r k).
  { case (decide (r = l)); intro.
    - exfalso. subst l. eauto with rtc.
    - unfold successor in Hsucc.
      rewrite -> successors_insert_ne in Hsucc by eauto.
      eauto. }
  econstructor; eauto with rtc.
Qed.

(* The combined storement. *)

Lemma rtc_successor_free r s l l' b :
  ¬ rtc (successor s) r l →
  rtc (successor (<[l:=b]> s)) r l' <->
  rtc (successor s) r l'.
Proof.
  split; eauto using rtc_successor_free_direct, rtc_successor_free_reverse.
Qed.

(* Analogous storements for group deallocation. *)

Lemma rtc_successor_deallocate_direct r s locs l' :
  rtc (successor s) r l' →
  (∀ l, l ∈ locs → ¬ rtc (successor s) r l) →
  rtc (successor (deallocate locs s)) r l'.
Proof.
  induction 1 as [| r ? l' Hsucc Hrtc IH ]; intros Hunreachable; econstructor.
  - case (decide (r ∈ locs)); intro Hr.
    { exfalso. apply Hunreachable in Hr. eauto with rtc. }
    { rewrite successor_deallocate_outside //. }
  - eapply IH. repeat intro. eapply (Hunreachable l); [ eauto |].
    eauto using successor_deallocate_implication with rtc.
Qed.

Lemma rtc_successor_deallocate_reverse r s locs l' :
  rtc (successor (deallocate locs s)) r l' →
  rtc (successor s) r l'.
Proof.
  induction 1 as [| r ? l' Hsucc Hrtc IH ]; econstructor;
  eauto using successor_deallocate_implication.
Qed.

Lemma rtc_successor_deallocate r s locs l' :
  (∀ l, l ∈ locs → ¬ rtc (successor s) r l) →
  rtc (successor (deallocate locs s)) r l' ↔
  rtc (successor s) r l'.
Proof.
  split; eauto using rtc_successor_deallocate_direct,
  rtc_successor_deallocate_reverse.
Qed.

(* If [l] is unreachable, then deallocating [l] does not alter which locations
   are reachable. *)

Lemma reachable_free s l l' :
  ¬ reachable s l →
  reachable (<[l:=deallocated]> s) l' <->
  reachable s l'.
Proof.
  intro. rewrite /reachable.
  split; intros (r & Hroot & Hrtc); exists r.
  - assert (l ≠ r).
    { intro. subst l. apply is_root_deallocated in Hroot. eauto. }
    rewrite -> is_root_insert_ne in Hroot by eauto.
    rewrite -> rtc_successor_free in Hrtc by eauto with reachable.
    eauto.
  - assert (l ≠ r).
    { intro. subst l. eauto with reachable. }
    rewrite -> is_root_insert_ne by eauto.
    rewrite -> rtc_successor_free by eauto with reachable.
    eauto.
Qed.

Local Lemma tautology1 (P Q : L → Prop) :
  (∀ r, P r ↔ Q r) →
  (∃ r, P r) ↔ (∃ r, Q r).
Proof.
  firstorder.
Qed.

Local Lemma tautology2 (A S C1 C2 : Prop) :
  (A → S ∧ (C1 ↔ C2)) →
  (A ∧ S) ∧ C1 ↔ A ∧ C2.
Proof.
  tauto.
Qed.

Lemma reachable_deallocate s locs l' :
  (∀ l, l ∈ locs → ¬ reachable s l) →
  reachable (deallocate locs s) l' <->
  reachable s l'.
Proof.
  intro Hunreachable. rewrite /reachable. apply tautology1; intro.
  rewrite is_root_deallocate //.
  apply tautology2; intro. split.
  + intro. eapply Hunreachable; eauto with reachable.
  + rewrite rtc_successor_deallocate //.
    repeat intro. eapply Hunreachable; eauto with reachable.
Qed.

(* If a region is closed under predecessors and contains no roots,
   then it is unreachable. *)

Lemma cannot_enter s locs :
  (∀ l l', l' ∈ locs → l' ∈ successors s l → l ∈ locs) →
  (∀ m m', rtc (successor s) m m' → m' ∈ locs → m ∈ locs).
Proof.
  unfold successor. induction 2; eauto.
Qed.

Lemma prove_unreachable_region s locs :
  (∀ l, l ∈ locs → ¬ is_root s l) →
  (∀ l l', l' ∈ locs → l' ∈ successors s l → l ∈ locs) →
  (∀ l, l ∈ locs → ¬ reachable s l).
Proof.
  intros Hnoroot Hclosed ?? (r & ? & ?).
  assert (¬ is_root s r). eauto using cannot_enter.
  eauto.
Qed.

Lemma prove_unreachable_singleton s l b :
  s !! l = Some b →
  ¬ is_stack_cell b →
  (∀ m, l ∈ successors s m → m = l) →
  ¬ reachable s l.
Proof.
  intros Hl Hnocell Hnopred.
  eapply (prove_unreachable_region s {[+l+]}).
  + intro. multiset. intro. subst.
    intros (b' & ? & ?). congruence.
  + intros ??. multiset. intro. subst. eauto.
  + by apply elem_of_singleton. (* FIXME: set_solver and multiset_solver fail *)
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [closed] and [reachable]. *)

Lemma closed_reachable_in_dom s l :
  closed s →
  reachable s l →
  l ∈ dom s.
Proof.
  intros Hclosed. intros (r & ? & Hrtc). eauto with in_dom.
Qed.

Local Hint Resolve closed_reachable_in_dom : in_dom.

(* [closed_insert] is used both when a new block is allocated and when
   an existing block is deallocated. *)

(* We could allow [pointers b ⊆ dom s ∪ {[+l+]}], but that does not seem
   useful. *)

Lemma closed_insert s l b :
  closed s →
  (∀l, l ∈ pointers b → l ∈ dom s) →
  closed (<[l:=b]> s).
Proof.
  intros Hclosed Hb.
  intros x y. unfold successor. intros Hsucc.
  case (decide (x = l)); [ intros; subst x | intros Hx ].
  { rewrite successors_insert in Hsucc.
    apply Hb in Hsucc. set_solver. }
  { rewrite -> successors_insert_ne in Hsucc by eauto.
    unfold closed in Hclosed.
    eauto with in_dom. }
Qed.

Lemma closed_insert_no_successors s l b :
  closed s →
  pointers b = ∅ →
  closed (<[l:=b]> s).
Proof.
  intros Hclosed Hb.
  eapply closed_insert; [ eauto |].
  rewrite Hb.
  set_solver.
Qed.

Lemma closed_insert_one_successor s l l' b :
  closed s →
  pointers b = {[+l'+]} →
  l' ∈ dom s →
  closed (<[l:=b]> s).
Proof.
  intros Hclosed Hb Hl'.
  eapply closed_insert; [ eauto |].
  rewrite Hb.
  intro m. rewrite gmultiset_elem_of_singleton.
  set_solver.
Qed.

Local Hint Resolve
  closed_insert_no_successors
  closed_insert_one_successor
: closed.

(* Allocating new blocks in the store does not make more memory locations
   accessible from an existing root [r]. This relies on the fact that the
   store is closed. *)

Lemma heap_path_already r s s' l :
  closed s →
  s ⊆ s' →
  r ∈ dom s →
  rtc (heap_edge s') r l →
  rtc (heap_edge s) r l.
Proof.
  induction 4 as [| r m l Hedge ? ? ]; [ eauto with rtc |].
  eapply heap_edge_already in Hedge; eauto.
  eauto with rtc.
Qed.

(* If, after an update of the stack cell [c], the location [l] is accessible
   via a heap path from some root [r], and if [c] and [r] are distinct, then
   this heap path already existed before this update. *)

Lemma heap_path_cell_update_reverse c cell s r l :
  rtc (heap_edge (<[c:=cell]> s)) r l →
  is_root s c →
  is_root (<[c:=cell]> s) c →
  r ≠ c →
  rtc (heap_edge s) r l.
Proof.
  induction 1 as [| r k l Hedge ? ? ]; intros.
  - eauto with rtc.
  - rewrite -> heap_edge_cell_update in Hedge by eauto.
    assert (c ≠ k).
    { intros ->. destruct Hedge. tauto. }
    eauto with rtc.
Qed.

(* The reciprocal storement. *)

Lemma heap_path_cell_update_direct c cell s r l :
  rtc (heap_edge s) r l →
  is_root s c →
  is_root (<[c:=cell]> s) c →
  r ≠ c →
  rtc (heap_edge (<[c:=cell]> s)) r l.
Proof.
  induction 1 as [| r k l Hedge ? ? ]; intros.
  - eauto with rtc.
  - rewrite <- heap_edge_cell_update in Hedge by eauto.
    assert (c ≠ k).
    { intros ->. destruct Hedge. tauto. }
    eauto with rtc.
Qed.

(* The combined storement. *)

Lemma heap_path_cell_update c cell s r l :
  is_root s c →
  is_root (<[c:=cell]> s) c →
  r ≠ c →
  rtc (heap_edge (<[c:=cell]> s)) r l <->
  rtc (heap_edge s) r l.
Proof.
  split; eauto using heap_path_cell_update_direct,
                     heap_path_cell_update_reverse.
Qed.

(* [reachable_from s P l] means that the [l] is reachable from some root [r]
   that satisfies [P r]. *)

Definition reachable_from s P l :=
  ∃ r, is_root s r ∧ rtc (heap_edge s) r l ∧ P r.

Hint Unfold reachable_from : reachable.

Lemma reachable_from_reachable s P l :
  reachable_from s P l →
  reachable s l.
Proof.
  destruct 1 as (r & ? & ? & ?). exists r.
  split; [ eauto |].
  eauto using heap_path_implies_path.
Qed.

Local Hint Resolve reachable_from_reachable : reachable.

(* If [c] is a root, then to be reachable is to be reachable from [c]
   or from some root other than [c]. *)

Lemma to_be_or_not_to_be s l c :
  is_root s c →
  reachable s l ↔
    reachable_from s (λ r : L, r ≠ c) l ∨
    rtc (heap_edge s) c l.
Proof.
  split.
  { intros Hreach.
    rewrite -> reachable_via_heap_path in Hreach.
    destruct Hreach as (r & ? & ?).
    case (decide (r = c)); intro; subst.
    + right. eauto.
    + left. eauto with reachable. }
  { intuition eauto with reachable. }
Qed.

(* If, after writing [c := cell], a memory location [l] is reachable from
   some root [r] other than [c], then it was already reachable from [r]
   prior to this update, and vice-versa. *)

Lemma reachable_from_cell_update_ne s c cell l :
  is_root s c →
  is_stack_cell cell →
  reachable_from (<[c:=cell]> s) (λ r, r ≠ c) l <->
  reachable_from s (λ r, r ≠ c) l.
Proof.
  split; intros (r & ? & ? & ?); exists r; repeat split; eauto.
  - rewrite <- heap_path_cell_update by eauto. eauto.
  - rewrite -> heap_path_cell_update by eauto. eauto.
Qed.

(* If, after writing [c := cell], a memory location [l] is reachable from
   the root [c], then either [l] is [c] or [l] was already reachable from
   some successor [r] of [c] prior to this update, and vice-versa. *)

Lemma reachable_from_cell_update_eq s c cell l :
  is_root s c →
  is_stack_cell cell →
  rtc (heap_edge (<[c:=cell]> s)) c l <->
  l = c ∨ ∃ r, ¬ is_root s r ∧ r ∈ pointers cell ∧ rtc (heap_edge s) r l.
Proof.
  intros ??. split.
  { inversion 1 as [| ? r ? Hedge Hpath ]; [ eauto | right; subst ].
    destruct Hedge as [ Hedge ? ].
    assert (r ≠ c) by (intros ->; eauto).
    assert (¬ is_root s r) by eauto.
    rewrite /successor /successors lookup_insert in Hedge.
    rewrite -> heap_path_cell_update in Hpath by eauto.
    eauto. }
  { intros [ ? | (r & ? & ? & Hpath) ].
    + subst l. eauto with rtc.
    + assert (heap_edge (<[c:=cell]> s) c r) by eauto.
      assert (r ≠ c) by (intros ->; eauto).
      rewrite <- heap_path_cell_update in Hpath by eauto.
      eauto with rtc. }
  (* Ouf. *)
Qed.

(* A combination of the previous two lemmas. *)

(* The reachable memory locations after writing [c := cell] are those that
   were already reachable from some root other than [c], plus [c] itself,
   plus the locations that were already reachable from [cell]. *)

(* This very precise (hence painful) update lemma is required in order to
   show that [store_agreement] is preserved by an update to a cell. *)

Lemma reachable_cell_update s c cell l :
  is_root s c →
  is_stack_cell cell →
  reachable (<[c:=cell]> s) l <->
    reachable_from s (λ r, r ≠ c) l ∨
    l = c ∨
    ∃ r, ¬ is_root s r ∧ r ∈ pointers cell ∧ rtc (heap_edge s) r l.
Proof.
  intros ??.
  rewrite <- reachable_from_cell_update_eq by eauto.
  rewrite <- reachable_from_cell_update_ne by eauto.
  eapply to_be_or_not_to_be. eauto.
Qed.

(* If, after allocating a block [b] at a fresh address [l] and updating the
   stack [c] with a pointer to this block, a memory location [l'] is
   reachable, then either [l'] is [c] or [l'] is [l] or [l'] was reachable
   already from some root other than [c]. The reverse implication holds as
   well. *)

(* This lemma seems really difficult to prove, because of the low-level
   reasoning that is involved. *)

Lemma reachable_alloc s c cell b l l' :
  closed s →
  is_root s c →
  is_stack_cell cell →
  pointers cell = {[+l+]} →
  s !! l = None →
  ¬ is_stack_cell b →
  pointers b = ∅ →
  reachable (<[c:=cell]>(<[l:=b]>s)) l' <->
  c = l' ∨ l = l' ∨ (reachable_from s (λ r, r ≠ c) l').
Proof.
  intros Hclosed Hroot ? Hcell Hl ? Hb.

  assert (l ≠ c).
  { intro. subst. destruct Hroot as (? & ? & ?). simplify_eq. }

  assert (l ∈ dom (<[c:=cell]> (<[l:=b]> s))) by eauto with in_dom.

  (* [c] has exactly one successor, which is [l]. *)
  assert (Honly: ∀m, successor (<[c:=cell]> (<[l:=b]> s)) c m <-> m = l).
  { intro. rewrite /successor successors_insert Hcell gmultiset_elem_of_singleton //. }

  (* [l] has no successor. *)
  assert (Hnone: ∀m, successor (<[c:=cell]> (<[l:=b]> s)) l m <-> False).
  { intro. rewrite /successor successors_insert_ne // successors_insert Hb.
    set_solver. }

  (* The only path out of [l] leads to [l] itself. *)
  assert (Hll: ∀m, rtc (heap_edge (<[c:=cell]> (<[l:=b]> s))) l m <-> m = l).
  { split; [| intros; subst; eauto with rtc ].
    intro Hpath.
    inversion Hpath as [| ? ? ? Hsucc _ eq ]; simplify_eq; clear Hpath.
    + eauto.
    + exfalso.
      destruct Hsucc as [ Hsucc _ ].
      rewrite -> Hnone in Hsucc.
      tauto. }

  (* The only paths out of [c] lead to [c] and [l]. *)
  assert (Hcc:
   ∀m, l ≠ m → rtc (heap_edge (<[c:=cell]> (<[l:=b]> s))) c m <-> m = c
  ).
  { intros m ?. split.
    + inversion 1 as [| ? ? ? Hsucc Hrest Hfoo ]; simplify_eq; [ eauto |].
      exfalso.
      destruct Hsucc as [ Hsucc _ ].
      rewrite -> Honly in Hsucc. subst.
      rewrite -> Hll in Hrest.
      eauto.
    + intros ->. eauto with rtc. }

  split.

  (* Left to right implication. *) -

  (* In the updated store, [l'] is reachable from [c], so it is reachable
     via a heap path. Let [r] be the root where this path originates. *)
  rewrite -> reachable_via_heap_path by eauto.
  intros (r & Hr & Hpath).

  assert (l ≠ r).
  { intro. subst.
    rewrite -> is_root_insert_ne in Hr by eauto.
    rewrite -> is_root_insert in Hr. tauto. }

  (* By cases. *)
  case (decide (r = c)); intro.

  (* Case: the root [r] is the cell [c]. *)
  { subst r.
    case (decide (l = l')); [ eauto | intro; left ].
    (* [l'] is accessible from [c], and is not [l], so [l'] must be [c]. *)
    rewrite -> Hcc in Hpath by eauto.
    eauto. }

  (* Case: the root [r] is not [c]. *)
  { right. right. exists r.
    do 2 rewrite -> is_root_insert_ne in Hr by eauto.
    split; [ eauto |]. split; [| eauto ].
    (* We must prove that [l'] was already reachable before. *)
    rewrite -> heap_path_cell_update in Hpath by eauto.
    eapply heap_path_already in Hpath; eauto with in_dom. }

  (* Right to left implication. *) -

  destruct 1 as [ ? | [ ? | (r & Hr & Hpath & ?) ]].

  (* Case: [l'] is [c]. *)
  { subst l'. eauto with reachable. }
  (* Case: [l'] is [l]. *)
  { subst l'. exists c. split; [ eauto |].
    econstructor; [ | eapply rtc_refl ].
    rewrite Honly //. }
  (* Case: [l'] was reachable before from some root other than [c]. *)
  { exists r.
    assert (l ≠ r).
    { intros ->. destruct Hr as (? & ? & ?). congruence. }
    split; [ eauto |].
    eapply heap_path_implies_path.
    rewrite -> heap_path_cell_update by eauto.
    eauto using heap_path_monotonic. }

Qed.

(* ------------------------------------------------------------------------ *)

(* The above lemmas are true, but several of them are overkill. I have seen
   the light, midway through. Here is a simpler lemma, which stores that the
   set of reachable objects does not increase when a memory block is updated,
   provided of course that the new pointers that are written to the block are
   pointers to reachable objects. *)

(* We begin by proving that, if there is a path from [r] to [m] after a heap
   update, then either this path existed already before the update, or a path
   existed from some location that appears in [b'] to the location [m]. *)

Lemma analyze_path_after_heap_update s l b b' r m :
  s !! l = Some b →
  rtc (successor (<[l := b']> s)) r m →
    rtc (successor s) r m ∨
    ∃ r, r ∈ pointers b' ∧ r ∉ pointers b ∧ rtc (successor s) r m.
Proof.
  induction 2 as [| r r' m Hedge Hpath IH ]; [ eauto with rtc |].
  case (decide (l = r)); intro.
  (* Case: the path of interest goes through the block at [l]. *)
  { subst l.
    rewrite -> successor_insert in Hedge.
    destruct IH as [ IH | IH ]; [| right; eauto ].
    case (decide (r' ∈ pointers b)); intro.
    (* Subcase: the path of interest goes through an edge that exists
       both before and after the update. Easy. *)
    - left. eauto using prove_successor with rtc.
    (* Subcase: the path of interest goes through an edge that is
       destroyed by the update. *)
    - right. exists r'. eauto. }
  (* Case: the path of interest does not go through [l]. Easy. *)
  { rewrite -> successor_insert_ne in Hedge by eauto.
    intuition eauto with rtc. }
Qed.

(* Here is the promised lemma: if [m] is reachable after the heap update
   [l := b'], then [m] was reachable already before this update. The side
   conditions are that every new pointer in [pointers b' ∖ pointers b] is
   to a reachable object and that the location [l] is not magically turned
   into a stack cell. *)

Lemma analyze_reachable_after_heap_update s l b b' m :
  s !! l = Some b →
  (∀ l, l ∈ pointers b' → l ∉ pointers b → reachable s l) →
  (is_stack_cell b' → is_stack_cell b) →
  reachable (<[l := b']> s) m →
  reachable s m.
Proof.
  intros Hl ? Hcell (r & Hroot & Hpath).
  eapply analyze_path_after_heap_update in Hpath; [| eauto ].
  destruct Hpath as [ ? | (r' & ? & ? & Hpath) ].
  - assert (is_root s r).
    { case (decide (l = r)); intro.
      - subst l. rewrite -> is_root_insert in Hroot.
        apply Hcell in Hroot.
        eauto.
      - rewrite -> is_root_insert_ne in Hroot by eauto.
        eauto. }
    eauto with reachable.
  - eauto with reachable.
Qed.

(* The following lemma is analogous to [analyze_path_after_heap_update], but
   concerns the case where a new heap block or stack cell is allocated. *)

(* If there is a path of [r] to [m] after this allocation, then either this
   path existed before, or there exists a path from the new block to [m]. *)

Lemma analyze_path_after_alloc s l b' r m :
  s !! l = None →
  rtc (successor (<[l := b']> s)) r m →
    rtc (successor s) r m ∨
    ∃ r, r ∈ pointers b' ∧ rtc (successor s) r m.
Proof.
  induction 2 as [| r r' m Hedge Hpath IH ]; [ eauto with rtc |].
  case (decide (l = r)); intro.
  (* Case: the path of interest goes through [l]. *)
  { subst l.
    rewrite -> successor_insert in Hedge.
    intuition eauto. }
  (* Case: the path of interest does not go through [l]. *)
  { rewrite -> successor_insert_ne in Hedge by eauto.
    intuition eauto with rtc. }
Qed.

(* The following lemma is analogous to [analyze_reachable_after_heap_update],
   but concerns the case where a new heap block or stack cell is allocated. *)

(* If [l ≠ m] and [m] is reachable after the allocation [l := b'], then [m]
   was reachable already before this update. The side condition is that every
   pointer in [pointers b'] is to a reachable object. *)

Lemma analyze_reachable_after_alloc s l b' m :
  s !! l = None →
  (∀ l, l ∈ pointers b' → reachable s l) →
  l ≠ m →
  reachable (<[l := b']> s) m →
  reachable s m.
Proof.
  intros Hl Hpointers ? (r & Hroot & Hpath).
  (* Proceeds by cases. *)
  eapply analyze_path_after_alloc in Hpath; [| eauto ].
  destruct Hpath as [ Hpath | (r' & ? & Hpath) ].
  (* Case: the path from [r] to [m] already existed before. *)
  (* Then, we must have [l ≠ r], as shown by the following argument. *)
  + case (decide (l = r)); intro.
    - subst r. elimtype False.
      (* The address [l] was not initially allocated, and we have [l ≠ m],
         so we cannot possibly have a path from [l] to [m]. *)
      destruct Hpath as [| r r' m Hedge Hpath ];
      eauto using nonexistent_successor.
    - (* The hypothesis [l ≠ r] implies that [r] remains a root,
         which implies that [m] remains reachable. *)
      eauto with reachable.
  (* Case: there is a path from the block [b'] to [m]. *)
  + eauto with reachable.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [block_evolution]. *)

Lemma block_evolution_monotonic_in_unreachable (u1 u2 : Prop) b b' :
  (u1 → u2) →
  block_evolution u1 b b' →
  block_evolution u2 b b'.
Proof.
  unfold block_evolution. tauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [store_evolution]. *)

Lemma store_evolution_reflexive s :
  store_evolution s s.
Proof.
  split; [ eauto |].
  intros l _ ?.
  left. eauto.
Qed.

Lemma store_evolution_transitive s1 s2 s3 :
  store_evolution s1 s2 ->
  store_evolution s2 s3 ->
  store_evolution s1 s3.
Proof.
  intros [HE1 Hb1] [HE2 Hb2].
  split.
  { apply leibniz_equiv in HE1.
    by rewrite HE1. }
  intros l Hl1 Hu1.
  assert (l ∈ dom s2) as Hl2 by (now apply HE1).
  specialize (Hb2 _ Hl2).
  destruct (Hb1 _ Hl1) as [->| (?&?)].
  { eapply block_evolution_monotonic_in_unreachable; try (apply Hb2).
    intros Hr2 Hr1.
    apply Hr2.
    eapply prove_reachable_implication with s1; try easy.
    intros l' Hl' ?.
    now destruct (Hb1 _ Hl'). }
  { right. split; try easy.
    by destruct Hb2 as [<-| (?&?)]. }
Qed.

Lemma store_evolution_preserves_closedness s s' :
  closed s →
  store_evolution s s' →
  closed s'.
Proof.
  unfold store_evolution.
  intros Hclosed (Hdom & Hevol).
  intros l l' Hsucc.
  assert (Hl: l ∈ dom s) by eauto with in_dom.
  specialize (Hevol l Hl).
  destruct Hevol as [ ? | (? & Hdealloc) ].
  { rewrite <- Hdom.
    assert (successor s l l') by rewrite same_successor //.
    eauto with in_dom. }
  (* A deallocated block has no successor. *)
  { exfalso. unfold successor, successors in Hsucc.
    rewrite -> lookup_lookup_total_dom in Hsucc by eauto with in_dom.
    rewrite Hdealloc in Hsucc.
    rewrite -> pointers_deallocated in Hsucc by eauto.
    set_solver. }
Qed.

Lemma store_evolution_preserves_successor s1 s2 l l' :
  store_evolution s1 s2 →
  closed s1 →
  reachable s1 l →
  successor s1 l l' <-> successor s2 l l'.
Proof.
  intros (Hdom & Hevol) ? Hreachable.
  assert (Hldom: l ∈ dom s1) by eauto with in_dom.
  specialize (Hevol l Hldom).
  unfold block_evolution in Hevol.
  destruct Hevol as [ Hevol |]; [| tauto ].
  rewrite same_successor //.
Qed.

Lemma store_evolution_preserves_rtc_successor r s1 s2 l :
  store_evolution s1 s2 →
  closed s1 →
  reachable s1 r →
  rtc (successor s1) r l <-> rtc (successor s2) r l.
Proof.
  intros; split; induction 1 as [| r k l Hsucc Hrtc IH ]; eauto with rtc.
  { assert (successor s2 r k).
    { rewrite <- store_evolution_preserves_successor by eauto. eauto. }
    eauto with rtc reachable. }
  { assert (successor s1 r k).
    { rewrite -> store_evolution_preserves_successor by eauto. eauto. }
    eauto with rtc reachable. }
Qed.

Lemma agreement_on_domain s1 s2 c :
  s1 !!! c = s2 !!! c →
  c ∈ dom s1 →
  c ∈ dom s2 →
  s1 !! c = s2 !! c.
Proof.
  intros.
  rewrite -> !lookup_lookup_total by rewrite -elem_of_dom //.
  congruence.
Qed.

Lemma store_evolution_preserves_stack_cells r s1 s2 cell :
  store_evolution s1 s2 →
  s1 !! r = Some cell →
  is_stack_cell cell →
  s2 !! r = Some cell.
Proof.
  intros (? & Hevol) Hr Hcell.
  assert (Hdom: r ∈ dom s1) by eauto with in_dom.
  specialize (Hevol r Hdom).
  rewrite <- Hr. symmetry.
  eapply agreement_on_domain; eauto with in_dom.
  assert (is_root s1 r) by (econstructor; eauto).
  assert (reachable s1 r) by eauto with reachable.
  destruct Hevol as [ Hevol | Hevol ].
  + tauto.
  + exfalso; tauto.
Qed.

Lemma store_evolution_preserves_is_root r s1 s2 :
  store_evolution s1 s2 →
  is_root s1 r <-> is_root s2 r.
Proof.
  (* Another painful proof of something that seems obvious. *)
  intros (? & Hevol). split; intros Hroot.
  - assert (Hdom: r ∈ dom s1) by eauto with in_dom.
    assert (r ∈ dom s2) by eauto with in_dom.
    specialize (Hevol r Hdom).
    assert (reachable s1 r) by eauto with reachable.
    destruct Hevol as [ Hevol | Hevol ].
    + rewrite -> is_root_reformulation, Hevol in Hroot by eauto.
      rewrite -> is_root_reformulation by eauto.
      eauto.
    + exfalso. tauto.
  - assert (r ∈ dom s2) by eauto with in_dom.
    assert (Hdom: r ∈ dom s1) by eauto with in_dom.
    specialize (Hevol r Hdom).
    destruct Hevol as [ Hevol | Hevol ].
    + rewrite -> is_root_reformulation, <- Hevol in Hroot by eauto.
      rewrite -> is_root_reformulation by eauto.
      eauto.
    + exfalso.
      (* A deallocated cell cannot be a root. *)
      destruct Hevol as [ _ Hdealloc ].
      destruct Hroot as (b & Hr & ?).
      erewrite lookup_total_correct in Hdealloc by eauto. subst b.
      eauto using stack_cell_not_deallocated.
Qed.

Lemma store_evolution_preserves_reachable s1 s2 l :
  store_evolution s1 s2 →
  closed s1 →
  reachable s1 l <-> reachable s2 l.
Proof.
  intros. split; intros (r & Hroot & Hpath); exists r; split.
  - rewrite -store_evolution_preserves_is_root //.
  - rewrite -store_evolution_preserves_rtc_successor //.
    eauto with reachable.
  - rewrite store_evolution_preserves_is_root //.
  - rewrite store_evolution_preserves_rtc_successor //.
    rewrite <- store_evolution_preserves_is_root in Hroot by eauto.
    eauto with reachable.
Qed.

Lemma store_evolution_preserves_store_agreement s1 s2 s :
  store_agreement s1 s →
  store_evolution s1 s2 →
  closed s1 →
  store_agreement s2 s.
Proof.
  intros Hag Hevol.
  destruct Hag as (? & ? & Hco).
  split; [| split ].
  { destruct Hevol as (Hdom & _). rewrite -Hdom //. }
  { intros l.
    rewrite <- store_evolution_preserves_reachable by eauto.
    eauto. }
  { intros l.
    rewrite <- store_evolution_preserves_reachable by eauto.
    intro.
    rewrite <- Hco by eauto.
    symmetry.
    assert (Hldom: l ∈ dom s1) by eauto with in_dom.
    destruct Hevol as (_ & Hevol).
    specialize (Hevol l Hldom).
    destruct Hevol; [| tauto ].
    assumption. }
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [collect]. *)

Lemma dom_collect s :
  dom (collect s) ≡ dom s.
Proof.
  eapply dom_imap. intros l.
  rewrite elem_of_dom /is_Some.
  split; intros (b & ?); exists b; [ eauto | tauto ].
Qed.

Lemma store_evolution_collect s :
  store_evolution s (collect s).
Proof.
  split.
  { rewrite dom_collect //. }
  intros l Hl.
  rewrite (lookup_total_alt (collect s)).
  rewrite /collect.
  rewrite map_lookup_imap.
  rewrite -> elem_of_dom in Hl.
  apply lookup_lookup_total in Hl.
  rewrite Hl. simpl.
  rewrite /block_evolution.
  case (decide (reachable s l)); eauto.
Qed.

(* ADDED *)
Lemma store_evolution_collect_strong s1 s2 :
  closed s1 ->
  store_evolution s1 s2 ->
  store_evolution s2 (collect s1).
Proof.
  intros ? Hs. generalize Hs; intros [Hd He].
  split.
  { rewrite dom_collect //. }
  intros l Hl. generalize Hl. intros ?.
  symmetry in Hd. apply Hd in Hl.
  rewrite -> elem_of_dom in Hl.
  apply lookup_lookup_total in Hl.
  destruct (He l) as [Hel|(Hel&?)].
  { now apply Hd. }
  { rewrite (lookup_total_alt (collect s1)).
    rewrite /collect.
    rewrite map_lookup_imap.
    rewrite -Hel Hl. simpl.
    rewrite /block_evolution.
    case (decide (reachable s1 l)); eauto.
    intros. rewrite store_evolution_preserves_reachable in n; eauto. }
  { right. rewrite -store_evolution_preserves_reachable; eauto.
    split; try easy. rewrite (lookup_total_alt (collect s1)).
    rewrite /collect map_lookup_imap. rewrite Hl.
    simpl. rewrite decide_False //. }
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [store_agreement]. *)

Lemma store_agreement_reflexive s :
  store_agreement s s.
Proof.
  split; [| split ].
  + eauto.
  + tauto.
  + eauto.
Qed.

Lemma store_agreement_symmetric s1 s2 :
  store_agreement s1 s2 →
  store_agreement s2 s1.
Proof.
  intros (Hdom & Hreach & Hco). split; [| split ].
  { eauto. }
  { intros l. rewrite Hreach. tauto. }
  { intros l. rewrite <- Hreach. intro. rewrite Hco //. }
Qed.

Lemma store_agreement_preserves_freshness s s' l :
  store_agreement s s' →
  s !! l = None →
  s' !! l = None.
Proof.
  destruct 1. eauto with in_dom.
Qed.

Lemma store_agreement_preserves_in_dom s1 s2 l :
  store_agreement s1 s2 →
  l ∈ dom s2 →
  l ∈ dom s1.
Proof.
  intros (Hdom & Hreach & Hco) Hl. rewrite Hdom //.
Qed.

Local Hint Resolve store_agreement_preserves_in_dom : in_dom.

Lemma store_agreement_at_reachable_cell_total s1 s2 l :
  store_agreement s1 s2 →
  reachable s1 l →
  s1 !!! l = s2 !!! l.
Proof.
  intros (Hdom & Hreach & Hco) Hl. eauto.
Qed.

Lemma store_agreement_at_reachable_cell s1 s2 l b :
  store_agreement s1 s2 →
  reachable s1 l →
  s2 !! l = Some b →
  s1 !! l = Some b.
Proof.
  intros ? ? Hl.
  rewrite <- Hl.
  eapply agreement_on_domain; [| eauto with in_dom | eauto with in_dom ].
  eauto using store_agreement_at_reachable_cell_total.
Qed.

Lemma store_agreement_at_stack_cell s1 s2 c cell :
  store_agreement s1 s2 →
  s2 !! c = Some cell →
  is_stack_cell cell →
  s1 !! c = Some cell.
Proof.
  intros (Hdom & Hreach & Hco) Hc ?.
  rewrite <- Hc.
  eapply agreement_on_domain; eauto with in_dom.
  eapply Hco.
  assert (is_root s2 c) by (econstructor; eauto).
  rewrite Hreach. eauto with reachable.
Qed.

Lemma store_agreement_preserves_is_root_direct s1 s2 c :
  store_agreement s1 s2 →
  is_root s1 c →
  is_root s2 c.
Proof.
  intros (Hdom & Hreach & Hco) Hroot.
  assert (c ∈ dom s1) by eauto with in_dom.
  assert (reachable s1 c) by eauto with reachable.
  revert Hroot.
  rewrite -> !is_root_reformulation by eauto.
  rewrite -> Hco by eauto.
  eauto.
Qed.

Lemma store_agreement_preserves_is_root s1 s2 c :
  store_agreement s1 s2 →
  is_root s1 c <->
  is_root s2 c.
Proof.
  split; eauto using store_agreement_preserves_is_root_direct,
                     store_agreement_symmetric.
Qed.

Lemma store_agreement_preserves_reachable s1 s2 l :
  store_agreement s1 s2 →
  reachable s1 l <->
  reachable s2 l.
Proof.
  intros (_ & Hreach & _). eauto.
Qed.

Lemma store_agreement_preserves_reachable_edge s1 s2 l l' :
  store_agreement s1 s2 →
  successor s1 l l' →
  reachable s1 l →
  successor s2 l l'.
Proof.
  intros (Hdom & Hreach & Hco) ? ?.
  rewrite <- same_successor by eauto with in_dom.
  eauto.
Qed.

Lemma store_agreement_preserves_reachable_heap_edge s1 s2 l l' :
  store_agreement s1 s2 →
  heap_edge s1 l l' →
  reachable s1 l →
  heap_edge s2 l l'.
Proof.
  intros Hag (? & Hnroot) ?.
  rewrite -> store_agreement_preserves_is_root in Hnroot by eauto.
  split; eauto using store_agreement_preserves_reachable_edge.
Qed.

(* TODO may be unused *)
Lemma store_agreement_preserves_reachable_path s1 s2 l l' :
  store_agreement s1 s2 →
  rtc (successor s1) l l' →
  reachable s1 l →
  rtc (successor s2) l l'.
Proof.
  induction 2 as [| l m l' Hedge ? ? ]; [ eauto with rtc |]; intros.
  econstructor.
  - eauto using store_agreement_preserves_reachable_edge.
  - eauto with reachable.
Qed.

Lemma store_agreement_preserves_reachable_heap_path s1 s2 l l' :
  store_agreement s1 s2 →
  rtc (heap_edge s1) l l' →
  reachable s1 l →
  rtc (heap_edge s2) l l'.
Proof.
  induction 2 as [| l m l' Hedge ? ? ]; [ eauto with rtc |]; intros.
  econstructor.
  - eauto using store_agreement_preserves_reachable_heap_edge.
  - eauto with reachable.
Qed.

Lemma store_agreement_preserves_reachable_from_direct s1 s2 P l :
  store_agreement s1 s2 →
  reachable_from s1 P l →
  reachable_from s2 P l.
Proof.
  intros ? (r & ? & ? & ?). exists r.
  rewrite -store_agreement_preserves_is_root //.
  eauto using store_agreement_preserves_reachable_heap_path with reachable.
Qed.

Lemma store_agreement_preserves_reachable_from s1 s2 P l :
  store_agreement s1 s2 →
  reachable_from s1 P l <->
  reachable_from s2 P l.
Proof.
  split; eauto using store_agreement_preserves_reachable_from_direct,
                     store_agreement_symmetric.
Qed.

Local Lemma tautology P Q R :
  Decision P →
  Decision Q →
  P ∨ Q ∨ R →
  P ∨ Q ∨ (¬P ∧ ¬Q ∧ R).
Proof.
  intros.
  case (decide P). tauto.
  case (decide Q). tauto.
  tauto.
Qed.

Lemma store_agreement_alloc s1 s2 c cell l b :
  store_agreement s1 s2 →
  closed s1 →
  closed s2 →
  is_root s1 c →
  is_stack_cell cell →
  pointers cell = {[+l+]} →
  ¬ is_stack_cell b →
  pointers b = ∅ →
  s1 !! l = None →
  store_agreement (<[c:=cell]>(<[l:=b]>s1)) (<[c:=cell]>(<[l:=b]>s2)).
Proof.
  intros Hag. intros.
  assert (Hc: is_root s2 c) by rewrite -store_agreement_preserves_is_root //.
  assert (s2 !! l = None).
  { rewrite -not_elem_of_dom.
    destruct Hag as (Hdom & _ & _).
    rewrite -Hdom not_elem_of_dom //. }
  assert (c ≠ l).
  { intros ->. destruct Hc as (? & ? & ?). congruence. }
  split; [| split ].
  - destruct Hag as (Hdom & Hreach & Hco).
    rewrite !dom_insert Hdom //.
  - intros l'.
    rewrite !reachable_alloc //.
    rewrite store_agreement_preserves_reachable_from //.
  - intros l'.
    rewrite !reachable_alloc //.
    intro hypothesis.
    apply tautology in hypothesis; [| typeclasses eauto | typeclasses eauto].
    destruct hypothesis as [ ? | [ ? | (? & ? & ?) ]].
    + subst l'. rewrite !lookup_total_insert //.
    + subst l'.
      rewrite lookup_total_insert_ne //.
      rewrite lookup_total_insert //.
      rewrite lookup_total_insert_ne //.
      rewrite lookup_total_insert //.
    + rewrite !lookup_total_insert_ne //.
      destruct Hag as (_ & _ & Hco).
      eauto with reachable.
Qed.

Lemma store_agreement_free s1 s2 l :
  store_agreement s1 s2 →
  l ∈ dom s2 →
  ¬ reachable s2 l →
  store_agreement s1 (<[l:=deallocated]> s2).
Proof.
  intros (Hdom & Hreach & Hco) ? Hunreachable. split; [| split ].
  (* The domains coincide. *)
  { rewrite Hdom dom_insert.
    set_solver. }
  (* The reachable locations are the same. *)
  { intros l'. rewrite Hreach reachable_free //. }
  (* At every reachable location, the memory is the same. *)
  { intros l' Hreachable.
    assert (l ≠ l') by (intro; subst; rewrite -> Hreach in Hreachable; tauto).
    rewrite lookup_total_insert_ne //.
    eauto. }
Qed.

Lemma store_agreement_deallocate s1 s2 locs :
  store_agreement s1 s2 →
  locs ⊆ dom s2 →
  (∀l, l ∈ locs → ¬ reachable s2 l) →
  store_agreement s1 (deallocate locs s2).
Proof.
  intros (Hdom & Hreach & Hco) Hlocs Hunreachable. split; [| split ].
  (* The domains coincide. *)
  { rewrite dom_deallocate //. }
  (* The reachable locations are the same. *)
  { intros l'. rewrite Hreach reachable_deallocate //. }
  (* At every reachable location, the memory is the same. *)
  { intros l' Hreachable.
    rewrite Hco //.
    assert (l' ∉ locs).
    { intro Hl'. rewrite -> Hreach in Hreachable.
      apply Hunreachable in Hl'. tauto. }
    rewrite /deallocate gmap_lookup_total_mset_outside //. }
Qed.

(* A heap path of out of a non-root cannot lead to a root. *)

Lemma heap_path_out_of_non_root s l c :
  rtc (heap_edge s) l c →
  ¬ is_root s l →
  is_root s c →
  False.
Proof.
  induction 1 as [| ??? Hedge ? ].
  { tauto. }
  { intros _. destruct Hedge. eauto. }
Qed.

(* Store agreement is preserved by an update to a stack cell, provided we
   are not making a previously-unreachable object reachable again. *)

(* A really painstaking proof. *)

Lemma store_agreement_cell_update s1 s2 c b b' :
  store_agreement s1 s2 →
  s1 !! c = Some b →
  is_stack_cell b →
  is_stack_cell b' →
  (∀ r, r ∈ pointers b' → reachable s1 r) →
  store_agreement (<[c:=b']> s1) (<[c:=b']> s2).
Proof.
  intros Hag. split; [| split ].
  (* Agreement on the domain. *)
  { destruct Hag as (Hdom & _ & _). rewrite !dom_insert Hdom //. }
  (* Agreement on the set of reachable locations. *)
  { intro m.
    assert (s2 !! c = Some b)
      by eauto using store_agreement_at_stack_cell, store_agreement_symmetric.
    rewrite -> !reachable_cell_update by eauto.
    rewrite -> store_agreement_preserves_reachable_from by eauto.
    match goal with |- ?A ∨ ?B ∨ ?C1 <-> ?A ∨ ?B ∨ ?C2 =>
      cut (C1 <-> C2)
    end; [ tauto | split; intros (r & ? & ? & ?); exists r ].
    + split; [| split ].
      - rewrite <- store_agreement_preserves_is_root by eauto. eauto.
      - eauto.
      - eauto using store_agreement_preserves_reachable_heap_path. (* subtle *)
    + assert (Hr: reachable s1 r) by eauto.
      rewrite -> store_agreement_preserves_reachable in Hr by eauto.
      split; [| split ].
      - rewrite -> store_agreement_preserves_is_root by eauto. eauto.
      - eauto.
      - eapply store_agreement_preserves_reachable_heap_path;
        eauto using store_agreement_symmetric. (* subtle, too *) }
  (* Agreement on the content of reachable locations. *)
  { intro m.
    rewrite -> reachable_cell_update by eauto.
    destruct Hag as (_ & Hreach & Hco).
    intros [ ? | [ ? | (r & ? & ? & ?) ]].
    + case (decide (m = c)); intros; subst.
      - rewrite !lookup_total_insert //.
      - rewrite !lookup_total_insert_ne //. eauto with reachable.
    + subst m. rewrite !lookup_total_insert //.
    + assert (m ≠ c).
      { intros ->. eauto using heap_path_out_of_non_root. }
      rewrite !lookup_total_insert_ne //.
      eapply Hco.
      eauto with reachable. }
  (* YES! @^#%$ RAAH *)
Qed.

(* Store agreement is preserved by an update to a heap block, provided we
   are not making a previously-unreachable object reachable again. *)

Lemma store_agreement_heap_update s1 s2 l b b' :
  store_agreement s1 s2 →
  reachable s2 l →
  s1 !! l = Some b →
  (∀ r, r ∈ pointers b' → r ∉ pointers b → reachable s1 r) →
  (is_stack_cell b' → is_stack_cell b) →
  store_agreement (<[l:=b']> s1) (<[l:=b']> s2).
Proof.
  intros Hag ? ? ? ?.
  (* In the proof of the previous lemma, I used a rather painstaking
     technique, where reachability after the update is characterized
     in an exact manner in terms of reachability before the update.
     It turns out that there is a simpler proof scheme, as follows. *)
  set (s'1 := <[l:=b']> s1).
  set (s'2 := <[l:=b']> s2).
  (* Prove a few trivial facts. *)
  assert (s2 !! l = Some b)
    by eauto using store_agreement_at_reachable_cell,
                   store_agreement_symmetric.
  assert (∀ m, reachable s1 m → reachable s2 m).
    by (intro; rewrite store_agreement_preserves_reachable //).
  assert (∀ m, reachable s2 m → reachable s1 m).
    by (intro; rewrite -store_agreement_preserves_reachable //).
  assert (dom s'1 ≡ dom s'2).
  { destruct Hag as (Hdom & _ & _). rewrite !dom_insert Hdom //. }
  assert (dom s'2 ≡ dom s'1) by eauto.
  (* On either side, every location that is reachable after the update
     was reachable already before the update. *)
  assert (∀ m, reachable s'1 m → reachable s1 m)
    by eauto using analyze_reachable_after_heap_update.
  assert (∀ m, reachable s'2 m → reachable s2 m)
    by eauto using analyze_reachable_after_heap_update.
  (* Furthermore, after the update, the two stores agree on the content
     of every block that was previously reachable. *)
  assert (∀ m, reachable s1 m → s'1 !!! m = s'2 !!! m).
  { intros. rewrite /s'1 /s'2.
    case (decide (l = m)); intro.
    - subst m. rewrite !lookup_total_insert //.
    - rewrite !lookup_total_insert_ne //.
      eauto using store_agreement_at_reachable_cell_total. }
  (* Thus, the two updated stores agree on the content of their reachable
     blocks. This implies that they have the same reachable blocks. *)
  assert (∀ m : L, reachable s'1 m ↔ reachable s'2 m).
  { eapply prove_reachable_coincidence; eauto. }
  (* We can now conclude. *)
  split; [| split ]; eauto.
Qed.

(* Store agreement is preserved by the allocation of a new heap block or stack
   cell, provided we are not making a previously-unreachable object reachable
   again. *)

Lemma store_agreement_alloc_cell s1 s2 l b' :
  store_agreement s1 s2 →
  s1 !! l = None →
  (∀ r, r ∈ pointers b' → reachable s1 r) →
  store_agreement (<[l:=b']> s1) (<[l:=b']> s2).
Proof.
  intros Hag ? ?.
  (* We follow the proof scheme of the previous lemma. *)
  set (s'1 := <[l:=b']> s1).
  set (s'2 := <[l:=b']> s2).
  (* Prove a few trivial facts. *)
  assert (s2 !! l = None)
    by eauto using store_agreement_preserves_freshness.
  assert (∀ m, reachable s1 m → reachable s2 m).
    by (intro; rewrite store_agreement_preserves_reachable //).
  assert (∀ m, reachable s2 m → reachable s1 m).
    by (intro; rewrite -store_agreement_preserves_reachable //).
  assert (dom s'1 ≡ dom s'2).
  { destruct Hag as (Hdom & _ & _). rewrite !dom_insert Hdom //. }
  assert (dom s'2 ≡ dom s'1) by eauto.
  (* On either side, every location other than [l] that is reachable
     after the update was reachable already before the update. *)
  assert (∀ m, l ≠ m → reachable s'1 m → reachable s1 m)
    by eauto using analyze_reachable_after_alloc.
  assert (∀ m, l ≠ m → reachable s'2 m → reachable s2 m)
    by eauto using analyze_reachable_after_alloc.
  (* Therefore, after the update, the two stores agree on the content
     of every reachable block. *)
  assert (∀ m, reachable s'1 m → s'1 !!! m = s'2 !!! m).
  { intros m Hm. rewrite /s'1 /s'2.
    case (decide (l = m)); intro.
    - subst m. rewrite !lookup_total_insert //.
    - rewrite !lookup_total_insert_ne //.
      eauto using store_agreement_at_reachable_cell_total. }
  assert (∀ m, reachable s'2 m → s'1 !!! m = s'2 !!! m).
  { intros m Hm. rewrite /s'1 /s'2.
    case (decide (l = m)); intro.
    - subst m. rewrite !lookup_total_insert //.
    - rewrite !lookup_total_insert_ne //.
      eauto using store_agreement_at_reachable_cell_total. }
  (* Thus, the two updated stores agree on the content of their reachable
     blocks. This implies that they have the same reachable blocks. *)
  assert (∀ m : L, reachable s'1 m ↔ reachable s'2 m).
  { eapply prove_reachable_coincidence; eauto. }
  (* We can now conclude. *)
  split; [| split ]; eauto.
Qed.

End Successors.

Global Hint Resolve prove_successor : closed.
