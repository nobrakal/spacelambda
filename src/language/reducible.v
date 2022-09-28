From Coq Require Import Program.Equality.
From stdpp Require Import gmap relations.

From glaneur.spacelang Require Import hypotheses successors.
From glaneur Require Import alt_semantics semantics_equivalence substitution.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* reducible *)

Definition reducible maxsize k t σ :=
  exists t' σ', alt_reduction maxsize k t σ t' σ'.

Lemma reducible_gc maxsize k t σ σ' :
  gc (k ∪ locs t) σ σ' ->
  reducible maxsize k t σ' ->
  reducible maxsize k t σ.
Proof.
  intros Hgc (t2,(σ2,Hstep)).
  apply alt_impl_gts in Hstep.
  eexists _,_.
  apply gts_impl_alt.
  inversion Hstep. subst.
  econstructor.
  { eapply gc_trans.
    { apply Hgc. }
    { apply H. } }
  { eauto. }
Qed.

Lemma reducible_let_val maxsize k x v t σ :
  reducible maxsize k (tm_let x (tm_val v) t) σ.
Proof.
  exists (subst' x v t), σ.
  eapply AltRedGCHead.
  { apply gc_id. }
  eauto with head_step.
Qed.

Lemma reducible_let_ctx maxsize k x t1 t2 σ :
  reducible maxsize (k ∪ locs t2) t1 σ ->
  reducible maxsize k (tm_let x t1 t2) σ.
Proof.
  intros (t1',(σ', Ha)).
  exists (fill_item (ctx_let x t2) t1').
  eexists.
  eapply AltRedCtx; try easy.
  { by compute. }
  by unfold locs.
Qed.

Lemma reducible_if maxsize r n t1 t2 σ :
  reducible maxsize r (tm_if (tm_val (val_nat n)) t1 t2) σ.
Proof.
  destruct (decide (n=0)).
  { eexists _,_.
    eapply AltRedGCHead;
    eauto using gc_id with head_step. }
  { eexists _,_.
    eapply AltRedGCHead;
    eauto using gc_id with head_step. }
Qed.

Lemma reducible_alloc maxsize r n σ :
  n <= available maxsize σ ->
  reducible maxsize r (tm_alloc (tm_val (val_nat n))) σ.
Proof.
  intros.
  eexists _,_.
  eapply AltRedGCHead.
  { apply gc_id. }
  eapply HeadAlloc; try easy.
  apply not_elem_of_dom.
  apply is_fresh.
Qed.

Ltac reduce_easy :=
  eexists _,_;
  eapply AltRedGCHead;
  [ apply gc_id | eauto with head_step].

Lemma reducible_bin_op maxsize r op n m σ :
  reducible maxsize r (tm_bin_op op (tm_val (val_nat n)) (tm_val (val_nat m))) σ.
Proof. reduce_easy. Qed.

Ltac reduce_store_load :=
  intros ? Hn2;
  apply lookup_lt_is_Some_2 in Hn2;
  destruct Hn2 as (?,?);
  reduce_easy.

Lemma reducible_load maxsize r l n vs σ :
  σ !! l = Some (BBlock vs) ->
  n < length vs ->
  reducible maxsize r (tm_load (tm_val (val_loc l)) (tm_val (val_nat n))) σ.
Proof. reduce_store_load. Qed.

Lemma reducible_store maxsize r l n v vs σ :
  σ !! l = Some (BBlock vs) ->
  n < length vs ->
  reducible maxsize r (tm_store (tm_val (val_loc l)) (tm_val (val_nat n)) (tm_val v)) σ.
Proof. reduce_store_load. Qed.

Lemma reducible_call maxsize self args vs body σ r :
  length args = length vs ->
  reducible maxsize r (tm_call (val_code self args body) (fmap tm_val vs)) σ.
Proof. reduce_easy. Qed.

Lemma reducible_context maxsize r E t σ :
  reducible maxsize (r ∪ locs E) t σ ->
  reducible maxsize r (fill_item E t) σ.
Proof.
  intros (t',(σ',?)).
  exists (fill_item E t'),σ'. eapply AltRedCtx; eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* If we can reduce, the we can still reduce after a gc.
   Particularly tricky. *)

Lemma reducible_prepone maxsize r t σ σ' :
  closed σ' ->
  gc (r ∪ locs t) σ' σ ->
  reducible maxsize r t σ' ->
  reducible maxsize r t σ.
Proof.
  intros Hclo Hgc (t',(σ1,Hstep)).
  destruct (deep_gc_prepone Hclo Hgc Hstep) as (σ1',?).
  eexists _,_. eauto.
Qed.
