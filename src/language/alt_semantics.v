From Coq Require Import Program.Equality.
From stdpp Require Import gmap relations.

From glaneur.spacelang Require Import hypotheses successors.
From glaneur Require Export rstore head_semantics gc store.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* Semantics with GC, parameterized by a context to allow GC under
   a context. *)

Inductive alt_reduction :
  nat -> (gset loc) ->
  tm → store →
  tm → store →  Prop
  :=
| AltRedCtx maxsize k t1 σ1 t2 σ2 E t1' t2' :
  t1' = fill_item E t1 ->
  t2' = fill_item E t2 ->
  alt_reduction maxsize (k ∪ locs E) t1 σ1 t2 σ2 ->
  alt_reduction maxsize k t1' σ1 t2' σ2
| AltRedGCHead maxsize k t1 σ1 σ1' t2 σ2 :
  gc (k ∪ locs t1) σ1 σ1' →
  head_step maxsize t1 σ1' t2 σ2 →
  alt_reduction maxsize k t1 σ1 t2 σ2.

(* A curryfied version *)
Definition alt_reduction' maxsize r : relation (tm*store):=
  fun '(t1,σ1) '(t2,σ2) => alt_reduction maxsize r t1 σ1 t2 σ2.

(* ------------------------------------------------------------------------ *)
(* Toward [alt_reduction_grow_store] *)

Lemma alt_reduction_grow_store maxsize k t σ t' σ' :
  alt_reduction maxsize k t σ t' σ' ->
  dom σ ⊆ dom σ'.
Proof.
  intros Hgs.
  dependent induction Hgs; try easy.
  rewrite (gc_dom H).
  eauto using head_step_grow_store.
Qed.

Lemma alt_reduction_weaken_ctx maxsize k1 k2 t σ t' σ' :
  k1 ⊆ k2 ->
  alt_reduction maxsize k2 t σ t' σ' ->
  alt_reduction maxsize k1 t σ t' σ'.
Proof.
  intros Hk Hgs. revert k1 Hk.
  dependent induction Hgs; intros k1 Hk; subst.
  (* ctx *)
  { eapply AltRedCtx; try easy.
    apply IHHgs.
    set_solver. }
  (* head *)
  { eapply (@AltRedGCHead _ _ _ _ σ1'); try easy.
    eapply gc_weak; try exact H.
    set_solver. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Toward [deep_gc_prepone] *)
Lemma head_gc_switch maxsize r t1 σ0 σ1 σ t2 σ2:
  closed σ0 ->
  locs t1 ⊆ r ->
  head_step maxsize t1 σ1 t2 σ2 ->
  gc r σ0 σ1 ->
  gc r σ0 σ ->
  exists σ1' σ2', gc r σ σ1' /\ head_step maxsize t1 σ1' t2 σ2'.
Proof.
  intros ? ? Hstep ? ?.
  inversion Hstep; subst; clear Hstep.
  all:(try (eexists _,_; split; eauto using gc_id with head_step; fail)).
  { destruct (@gc.gc_diamond r σ0 σ1 σ) as (θ,(Hσ1&?)); try easy.
    exists θ, (<[l:=BBlock (replicate n val_unit)]> θ). split; try easy.
    eapply HeadAlloc; eauto.
    { apply not_elem_of_dom.
      apply gc_dom in Hσ1. rewrite <- Hσ1.
      apply not_elem_of_dom. eauto. }
    { apply gc_non_size_increasing in Hσ1. lia. } }
  all:assert (l∈r) by set_solver.
  { exists σ,σ. split; try apply gc_id.
    eapply HeadLoad; eauto.
    apply gc_read_root with (r:=r) (σ:=σ0); eauto.
    apply gc_read_root_inv with (r:=r) (σ':=σ2); eauto. }
  { exists σ,(insert l (BBlock (insert n v bs)) σ).
    split; try apply gc_id.
    eapply HeadStore; eauto.
    apply gc_read_root with (r:=r) (σ:=σ0); eauto.
    apply gc_read_root_inv with (r:=r) (σ':=σ1); eauto. }
Qed.

(* Under a closed store, we can prepone a gc, that is,
   if we are able to reduce, we can "make a gc in the past",
   and still be able to make a step. *)
Lemma deep_gc_prepone maxsize r t σ σ' t' σ1 :
  closed σ' ->
  gc (r ∪ locs t) σ' σ ->
  alt_reduction maxsize r t σ' t' σ1 ->
  exists σ1', alt_reduction maxsize r t σ t' σ1'.
Proof.
  intros Hclo Hgc Hstep.
  revert Hclo σ Hgc.
  dependent induction Hstep; subst; intros Hclo σ Hgc.
  { destruct (IHHstep Hclo σ) as (σ1',?).
    { rewrite locs_fill_item , assoc_L in Hgc. eauto. apply _. }
    { exists σ1'. eapply AltRedCtx; eauto. } }
  { assert (locs t1 ⊆ k ∪ locs t1) as Hs1 by set_solver.
    destruct (head_gc_switch Hclo Hs1 H0 H Hgc) as (?,(?,(?&?))).
    eexists. eapply AltRedGCHead; eauto. }
Qed.
