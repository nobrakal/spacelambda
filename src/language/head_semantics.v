From stdpp Require Import sets gmap gmultiset.
From spacelambda Require Import substitution.
From spacelambda Require Export store.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* The actual semantics *)

Definition exec_nat_bin_op op :=
  match op with
  | NatAdd => Nat.add
  | NatMul => Nat.mul
  | NatSub => Nat.sub end.

Definition exec_bool_bin_op op :=
  match op with
  | BoolAnd => andb
  | BoolOr => orb end.

Definition eval_call_prim p vs :=
  match p,vs with
  | prim_bool_op1 BoolNeg, [val_bool b] => Some (val_bool (negb b))
  | prim_bool_op2 op, [val_bool b1; val_bool b2] => Some (val_bool (exec_bool_bin_op op b1 b2))
  | prim_nat_op op, [val_nat m; val_nat n] => Some (val_nat (exec_nat_bin_op op m n))
  | prim_eq, [val_loc l1; val_loc l2] => Some (val_bool (bool_decide (l1=l2)))
  | prim_eq, [val_nat m; val_nat n] => Some (val_bool (bool_decide (m=n)))
  | _,_ => None end.

(* A head step *)
Inductive head_step : nat -> tm -> store -> tm -> store -> Prop :=
| HeadLet : forall s σ1 σ2 t1 t2 x v,
    t1 = tm_val v ->
    σ1 = σ2 ->
    head_step s
      (tm_let x t1 t2) σ1
      (subst' x v t2) σ2
| HeadCall : forall s σ t1 ts self args body vs,
    t1 = tm_val (val_code self args body) ->
    ts = fmap tm_val vs ->
    head_step s
      (tm_call t1 ts) σ
      (substs' (zip (self::args) (val_code self args body::vs)) body) σ
| HeadCallPrim : forall s σ t1 p ts vs v,
    t1 = tm_val (val_prim p) ->
    ts = fmap tm_val vs ->
    eval_call_prim p vs = Some v ->
    head_step s
      (tm_call t1 ts) σ
      (tm_val v) σ
| HeadIf : forall s σ t1 t2 t3 b,
    t1 = tm_val (val_bool b) ->
    head_step s
      (tm_if t1 t2 t3) σ
      (if b then t2 else t3) σ
| HeadAlloc : forall s σ σ' l t1 n bs,
    σ !! l = None →
    t1 = tm_val (val_nat n) ->
    bs = BBlock (replicate n val_unit) ->
    σ' = <[l:=bs]> σ →
    n <= s - size_heap σ  ->
    head_step s
      (tm_alloc t1) σ
      (tm_val (val_loc l)) σ'
| HeadLoad : forall s σ l t1 t2 n v bs,
    t1 = tm_val (val_loc l) ->
    σ !! l = Some (BBlock bs) ->
    t2 = tm_val (val_nat n) ->
    bs !! n = Some v ->
    head_step s
      (tm_load t1 t2) σ
      (tm_val v) σ
| HeadStore : forall s σ σ' t1 t2 t3 l n v bs,
    t1 = tm_val (val_loc l) ->
    t2 = tm_val (val_nat n) ->
    t3 = tm_val v ->
    σ !! l = Some (BBlock bs) ->
    σ' = insert l (BBlock (insert n v bs)) σ ->
    head_step s
      (tm_store t1 t2 t3) σ
      (tm_val (val_unit)) σ'
.

#[export] Hint Constructors head_step : head_step.

Lemma head_step_grow_store maxsize t1 σ1 t2 σ2 :
  head_step maxsize t1 σ1 t2 σ2 ->
  dom (gset loc) σ1 ⊆ dom _ σ2.
Proof.
  inversion_clear 1; subst; try easy; set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* Inversion lemmas *)

Lemma invert_head_step_alloc maxsize n σ t' σ' :
  head_step maxsize (tm_alloc (tm_val (val_nat n))) σ t' σ' ->
  exists l, t' = tm_val (val_loc l)
       /\ σ !! l = None
       /\ σ' = <[l:=BBlock (replicate n val_unit)]> σ
       /\ n <= maxsize - size_heap σ.
Proof.
  inversion_clear 1; subst.
  exists l; split; try easy.
  injection H1. intros ->. simpl.
  easy.
Qed.

Ltac rev_inject H :=
  injection H; intros <-.

Lemma invert_head_step_if s b t1 t2 σ t' σ' :
  head_step s (tm_if (tm_val (val_bool b)) t1 t2) σ t' σ' ->
  σ = σ' ∧ (t' = if b then t1 else t2).
Proof.
  inversion_clear 1.
  rev_inject H0. eauto.
Qed.

Lemma invert_head_step_load s (l:loc) (n:nat) σ t' σ' :
  head_step s (tm_load l n) σ t' σ' ->
  σ = σ' /\ (exists bs v, σ !! l = Some (BBlock bs) /\ t' = tm_val v /\ bs !! n = Some v).
Proof.
  inversion_clear 1.
  rev_inject H0.
  rev_inject H2.
  split; try easy.
  eexists _,_.
  rewrite H1,H3.
  easy.
Qed.

Lemma invert_head_step_store s (l:loc) (n:nat) (v:val) σ t' σ' :
  head_step s (tm_store l n v) σ t' σ' ->
  exists bs, σ !! l = Some (BBlock bs)
        /\ σ' = <[l:=BBlock (<[n:=v]> bs)]> σ
        /\ t' = tm_val val_unit.
Proof.
  inversion_clear 1. subst.
  eexists _.
  rev_inject H0.
  rev_inject H1.
  rev_inject H2.
  rewrite H3.
  easy.
Qed.

Lemma invert_head_step_call s self args body vs σ t' σ' :
  head_step s (tm_call (val_code self args body) (fmap tm_val vs)) σ t' σ' ->
  σ = σ' /\ t' = substs' (zip (self::args) (val_code self args body::vs)) body.
Proof.
  inversion_clear 1; subst.
  split; try easy.
  apply fmap_inj in H1.
  2:{ intros ? ? E. now injection E. }
  rev_inject H0. intros. subst. eauto.
  inversion H0.
Qed.

Lemma invert_head_step_call_prim s prim vs σ t' σ' :
  head_step s (tm_call (val_prim prim) (fmap tm_val vs)) σ t' σ' ->
  σ = σ' ∧ exists v, t' = tm_val v /\ eval_call_prim prim vs = Some v.
Proof.
  inversion_clear 1.
  inversion H0.
  rev_inject H0.
  apply fmap_inj in H1.
  2:{ intros ? ? E. now injection E. }
  subst. eauto.
Qed.
