From Coq Require Import Program.Equality.
From stdpp Require Import gmap relations.

From glaneur.spacelang Require Import hypotheses successors.
From glaneur Require Import alt_semantics semantics_equivalence semantics substitution.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* Some inversion lemmas *)

Lemma head_step_no_val maxsize t1 σ1 t2 σ2 :
  head_step maxsize t1 σ1 t2 σ2 ->
  to_val t1 = None.
Proof.
  inversion 1; subst; easy.
Qed.

Lemma alt_reduction_no_val maxsize k t1 σ1 t2 σ2 :
  alt_reduction maxsize k t1 σ1 t2 σ2 ->
  to_val t1 = None.
Proof.
  inversion 1; subst.
  { by destruct E. }
  { inversion H1; eauto using head_step_no_val. }
Qed.

Lemma step_no_val maxsize t1 σ1 t2 σ2 :
  step maxsize t1 σ1 t2 σ2 ->
  to_val t1 = None.
Proof.
  inversion 1; subst.
  { by destruct E. }
  { inversion H0; eauto using head_step_no_val. }
Qed.

Lemma invert_must_be_head maxsize t1 σ1 t2 σ2 :
  (forall E t t', t1 = fill_item E t -> step maxsize t σ1 t' σ2 -> False) ->
  step maxsize t1 σ1 t2 σ2 ->
  head_step maxsize t1 σ1 t2 σ2.
Proof.
  intros Hnd.
  inversion_clear 1; subst; try easy.
  exfalso. by eapply Hnd.
Qed.

Ltac cannot_be_distant :=
  intros [] ? ?; try easy;
  inversion_clear 1; try easy;
  intros E; apply step_no_val in E;
  easy.

Ltac invert_head :=
  intros Hstep;
  apply alt_impl_gts in Hstep;
  inversion_clear Hstep as [? ? ? ? ? ? ? ? Hdstep]; subst;
  apply invert_must_be_head in Hdstep; last first.

Lemma invert_step_let_val maxsize k x (v:val) t σ t' σ' :
  alt_reduction maxsize k (tm_let x v t) σ t' σ' ->
  t' = subst' x v t /\ gc (k ∪ (locs v ∪ locs t)) σ σ'.
Proof.
  invert_head.
  { cannot_be_distant. }
  inversion_clear Hdstep; try easy; subst.
  injection H0. intros ->.
  easy.
Qed.

Lemma has_to_be_val vs l l' t :
  to_val t = None ->
  tm_val <$> vs = (tm_val <$> l) ++ t :: l' ->
  False.
Proof.
  revert l l' t. induction vs; intros l l' t; intros ? Heq.
  { destruct l; try easy. }
  { destruct l; injection Heq; intros; subst; now eauto. }
Qed.

Lemma head_step_no_ctx maxsize E t σ t' σ' :
  to_val t = None ->
  head_step maxsize (fill_item E t) σ t' σ' ->
  False.
Proof.
  intros ? Hstep.
  inversion Hstep; subst;
    destruct E; simpl in *; inversion H0; subst; try easy.
  eauto using has_to_be_val.
Qed.

Lemma invert_step_context maxsize k E t σ t' σ' :
  to_val t = None ->
  alt_reduction maxsize k (fill_item E t) σ t' σ' ->
  exists t'',
    t' = fill_item E t'' /\
      alt_reduction maxsize (k ∪ locs E) t σ t'' σ'.
Proof.
  inversion_clear 2; subst.
  (* ctx *)
  { apply fill_item_inj in H1; eauto using alt_reduction_no_val.
    destruct H1 as (->&->).
    eauto. }
  (* head step *)
  { exfalso.
    eauto using head_step_no_ctx. }
Qed.

Lemma invert_step_if maxsize k (n:nat) t1 t2 σ t' σ' :
  alt_reduction maxsize k (tm_if n t1 t2) σ t' σ' ->
  gc (k ∪ locs t1 ∪ locs t2) σ σ' /\
    ((n ≠ 0 /\ t' = t1) \/ (n = 0 /\ t' = t2)).
Proof.
  invert_head.
  { cannot_be_distant. }
  apply invert_head_step_if in Hdstep.
  destruct Hdstep as (->&Hif).
  split; try easy.
  eapply (gc_weak H).
  set_solver.
Qed.

Lemma invert_step_alloc maxsize k (n:nat) σ t' σ' :
  alt_reduction maxsize k (tm_alloc n) σ t' σ' ->
  exists l σ1,  t' = tm_val (val_loc l)
           /\ σ !! l = None
           /\ σ' = (<[l:=BBlock (replicate n val_unit)]> σ1)
           /\ n <= available maxsize σ1
           /\ gc k σ σ1.
Proof.
  invert_head.
  { cannot_be_distant. }
  destruct (invert_head_step_alloc Hdstep) as (l,(?&H1l&H2l&?)).
  exists l. exists σ1'. split; try easy.
  split; try easy.
  { apply gc_dom in H.
    apply not_elem_of_dom.
    apply not_elem_of_dom in H1l.
    by rewrite H. }
  { rewrite right_id_L in H; try apply _.
    rewrite H2l. easy. }
Qed.

Lemma invert_step_bin_op maxsize k op (n m:nat) σ t' σ' :
  alt_reduction maxsize k (tm_bin_op op n m) σ t' σ' ->
  gc k σ σ' ∧ t' = tm_val (val_nat (exec_bin_op op n m)).
Proof.
  invert_head.
  { cannot_be_distant. }
  destruct (invert_head_step_bin_op Hdstep) as (->,?).
  split; try easy.
  apply (gc_weak H).
  set_solver.
Qed.

Lemma invert_step_load maxsize k (l:loc) (n:nat) σ t' σ' :
  alt_reduction maxsize k (tm_load l n) σ t' σ' ->
  gc (k ∪ {[l]}) σ σ' /\ (exists bs v, σ' !! l = Some (BBlock bs) /\ t' = tm_val v /\ bs !! n = Some v).
Proof.
  invert_head.
  { cannot_be_distant. }
  apply invert_head_step_load in Hdstep.
  destruct Hdstep as (?,(bs,(v,(Hs&?&Hn)))). subst.
  split; try easy.
  { apply (gc_weak H). set_solver. }
  eexists _,_. rewrite Hs,Hn. easy.
Qed.

Lemma invert_step_store maxsize r (l:loc) (n:nat) (v:val) σ t' σ' :
  alt_reduction maxsize r (tm_store l n v) σ t' σ' ->
  exists σ1 bs, gc (r ∪ {[l]} ∪ locs v) σ σ1
           /\ σ1 !! l = Some (BBlock bs)
           /\ σ' = <[l:=BBlock (<[n:=v]> bs)]> σ1
           /\ t' = tm_val val_unit.
Proof.
  invert_head.
  { cannot_be_distant. }
  apply invert_head_step_store in Hdstep.
  destruct Hdstep as (bs,(?&?&->)). subst.
  eexists _,_.
  split; try easy.
  { apply (gc_weak H). set_solver. }
  split; try easy.
  easy.
Qed.

Lemma invert_step_call maxsize r self args body vs σ t' σ' :
  alt_reduction maxsize r (tm_call (val_code self args body) (fmap tm_val vs)) σ t' σ' ->
  gc (r ∪ locs vs) σ σ' /\ t' = substs' (zip (self::args) (val_code self args body::vs)) body.
Proof.
  invert_head.
  { intros [] ? ?; try easy; simpl;
      intros E; injection E; clear E.
    { intros _ ? Hd. apply step_no_val in Hd. subst. easy. }
    intros E.
    assert (exists v, t0 = tm_val v) as (?,->).
    { apply (f_equal (lookup (length l))) in E.
      rewrite list_lookup_fmap, list_lookup_middle in E; try easy.
      destruct (vs !! length l); try easy. injection E.
      intros <-. now eexists. now rewrite fmap_length. }
    intros _ Hd. apply step_no_val in Hd. easy. }
  apply invert_head_step_call in Hdstep.
  destruct Hdstep as (->&?).
  split; try easy.
  apply (gc_weak H). auto_locs.
  set_solver.
Qed.
