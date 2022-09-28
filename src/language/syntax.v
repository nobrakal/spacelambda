From Coq Require Import Wellfounded.

From stdpp Require Import binders gmap gmultiset.

(* ------------------------------------------------------------------------ *)
(* Syntax of SpaceLambda *)

(* Locations are modeled with Z, any countable set would work. *)
Notation loc := Z.

(* Operations on natural numbers. *)
Inductive op := OpAdd | OpMul | OpSub.

(* Values and terms are mutually recursive, as we model code pointers as
   closed terms. *)
Inductive val : Type :=
| val_loc : loc -> val
| val_nat : nat -> val
| val_unit : val
| val_code : binder -> list binder -> tm -> val with
tm : Type :=
(* values *)
| tm_val : val -> tm
(* call *)
| tm_call : tm -> list tm -> tm
(* let *)
| tm_var : string -> tm
| tm_let : binder -> tm -> tm -> tm
(* naturals *)
| tm_bin_op : op -> tm -> tm -> tm
| tm_if : tm -> tm -> tm -> tm
(* Blocks *)
| tm_alloc : tm -> tm
| tm_load  : tm -> tm -> tm
| tm_store : tm -> tm -> tm -> tm
.

Coercion val_nat : nat >-> val.
Coercion val_loc : loc >-> val.
Coercion tm_val : val >-> tm.
Coercion tm_var : string >-> tm.

Global Instance inhabited_val : Inhabited val := populate val_unit.
Global Instance inhabited_tm  : Inhabited tm  := populate (tm_val inhabitant).

(* ------------------------------------------------------------------------ *)
(* For well founded recursion. *)

(* A size function for well founded recursion over tm. *)
Fixpoint tm_size (t : tm):= 1 +
  match t with
  | tm_var _ => 0
  | tm_val v => val_size v
  | tm_call t1 xs => tm_size t1 + list_sum (tm_size <$> xs)
  | tm_let _ t1 t2 | tm_bin_op _ t1 t2 | tm_load t1 t2 => tm_size t1 + tm_size t2
  | tm_alloc t1 => tm_size t1
  | tm_store t1 t2 t3 | tm_if t1 t2 t3 => tm_size t1 + tm_size t2 + tm_size t3
  end with
val_size v :=
  match v with
  | val_code _ _ t => tm_size t
  | _ => 0 end.

Lemma tm_size_non_zero t :
  tm_size t ≠ 0.
Proof. destruct t; simpl; lia. Qed.

(* ------------------------------------------------------------------------ *)
(* Contexts. *)

(* Contexts are non-recursive *)
Inductive ctx :=
| ctx_let : binder -> tm -> ctx (* let x = ◻ in t *)
| ctx_call1 : list val -> ctx (* call ◻ vs *)
| ctx_call2 : tm -> list val -> list tm -> ctx (* call t (vs ++ ◻ :: ts) *)
| ctx_bin_op1 : op -> tm -> ctx (* ◻ (op) t *)
| ctx_bin_op2 : op -> val -> ctx (* v (op) ◻ *)
| ctx_if : tm -> tm -> ctx (* if ◻ then t1 else t2 *)
| ctx_alloc : ctx (* alloc ◻ *)
| ctx_load1 : tm -> ctx (* load ◻ t *)
| ctx_load2 : val -> ctx (* load v ◻ *)
| ctx_store1 : tm -> tm -> ctx (* store ◻ t1 t2 *)
| ctx_store2 : val -> tm -> ctx (* store v ◻ t *)
| ctx_store3 : val -> val -> ctx (* store v1 v2 ◻ *)
.

Definition fill_item (E:ctx) (t:tm) : tm :=
  match E with
  | ctx_let x t2 => tm_let x t t2
  | ctx_call1 xs => tm_call t (tm_val <$> xs)
  | ctx_call2 t1 xs ys => tm_call t1 ((tm_val <$> xs) ++ t :: ys)
  | ctx_bin_op1 op t2 => tm_bin_op op t t2
  | ctx_bin_op2 op v => tm_bin_op op (tm_val v) t
  | ctx_if t2 t3 => tm_if t t2 t3
  | ctx_alloc => tm_alloc t
  | ctx_load1 t2 => tm_load t t2
  | ctx_load2 v => tm_load (tm_val v) t
  | ctx_store1 t1 t2 => tm_store t t1 t2
  | ctx_store2 v t2 => tm_store (tm_val v) t t2
  | ctx_store3 v1 v2 => tm_store (tm_val v1) (tm_val v2) t
  end.

Definition to_val (t:tm) : option val :=
  match t with
  | tm_val v => Some v
  | _ => None end.

Lemma ctx_list_length xs xs' t t' ys ys' :
  to_val t = None ->
  to_val t' = None ->
  (tm_val <$> xs) ++ t :: ys = (tm_val <$> xs') ++ t' :: ys' ->
  length xs = length xs'.
Proof.
  revert xs' t t' ys ys'.
  induction xs; intros xs' t t' ys ys' ? ? Heq; simpl in *.
  { destruct xs'; try easy.
    injection Heq. intros. subst. easy. }
  { destruct xs'.
    { exfalso. simpl in *. injection Heq. intros. subst. easy. }
    { simpl. injection Heq. intros Heq' ?. f_equal. subst. eapply IHxs.
      3:eauto. all:eauto. } }
Qed.

Lemma middle_list {A:Type} (l:list A) x l1 l2 :
  l = l1 ++ x::l2 ->
  l !! length l1 = Some x.
Proof.
  intros ->.
  rewrite list_lookup_middle; easy.
Qed.

(* If t and t' are not values, then fill_item is injective. *)
Lemma fill_item_inj E t E' t' :
  to_val t = None ->
  to_val t' = None ->
  fill_item E t = fill_item E' t' ->
  E = E' /\ t = t'.
Proof.
  intros ? ? Heq.
  assert (Inj eq eq tm_val) as Hinj.
  { intros ? ? Heq'. injection Heq'. easy. }
  destruct E,E'; simpl in *; try congruence; injection Heq; intros; subst; try easy.
  { apply fmap_inj in H1; subst; easy. }
  { exfalso.
    apply middle_list in H1.
    rewrite fmap_length, list_lookup_fmap in H1.
    destruct (l !! length l0); try easy. injection H1. intros <-.
    simpl in *. congruence. }
  { exfalso. symmetry in H1.
    apply middle_list in H1.
    rewrite fmap_length, list_lookup_fmap in H1.
    destruct (l1 !! length l); try easy. injection H1. intros <-.
    simpl in *. congruence. }
  { assert (length l = length l1).
    { eauto using ctx_list_length. }
    apply app_inj_1 in H1. 2:{ now do 2 rewrite fmap_length. }
    destruct H1 as (Hl1&Hl2). injection Hl2. clear Hl2. intros -> ->.
    split; try easy.
    apply fmap_inj in Hl1; subst; easy. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Implicit Types *)
Implicit Type v : val.
Implicit Type t : tm.
Implicit Type E : ctx.

(* ------------------------------------------------------------------------ *)
(* Locations of a value *)

(* The base function, return the list of pointers followed by the GC
   in a value *)
Definition val_pointer_list (v:val) : list loc :=
  match v with
  | val_loc l => [l]
  | val_unit | val_nat _ => []
  (* We consider code pointers, without any outgoing pointers.
     This is coherent with the substitution defined above, which does not
     substitute inside code pointers. *)
  | val_code _ _ _ => [] end.

(* We define a typeclass to define [locs],
   a function returning a set of locations.*)
Class Location A := locs : A -> gset loc.

Definition locs_val (v:val) : gset loc :=
  list_to_set (val_pointer_list v).

Global Instance location_val : Location val := locs_val.

Lemma locs_val_alt v :
  locs_val v = match v with | val_loc l => {[l]} | _ => ∅ end.
Proof.
  destruct v; try easy.
  unfold locs_val. simpl.
  rewrite right_id_L; try easy.
  apply _.
Qed.

Lemma locs_val_unit : locs_val (val_unit) = ∅.
Proof. easy. Qed.

Lemma locs_val_nat n : locs_val (val_nat n) = ∅.
Proof. easy. Qed.

Lemma locs_val_code self args body : locs_val (val_code self args body) = ∅.
Proof. easy. Qed.

Lemma locs_val_loc l :
  locs_val (val_loc l) = {[l]}.
Proof. now rewrite locs_val_alt. Qed.

#[export] Hint Rewrite
 locs_val_unit locs_val_nat locs_val_code locs_val_loc : rew_locs_val.
Ltac auto_locs_val :=
  autorewrite with rew_locs_val.

Definition locs_list `{Location A} (ls:list A) : gset loc :=
  ⋃ (locs <$> ls).

Global Instance location_list `{Location A} : Location (list A) := locs_list.

Fixpoint locs_tm (t:tm) : gset loc :=
  match t with
  | tm_val v => locs_val v
  | tm_call t1 xs => locs_tm t1 ∪ ⋃ (locs_tm <$> xs)
  | tm_let _ t1 t2 => locs_tm t1 ∪ locs_tm t2
  | tm_var _ => ∅
  | tm_bin_op _ t1 t2 => locs_tm t1 ∪ locs_tm t2
  | tm_if t1 t2 t3 => locs_tm t1 ∪ locs_tm t2 ∪ locs_tm t3
  | tm_alloc t1 => locs_tm t1
  | tm_load t1 t2 => locs_tm t1 ∪ locs_tm t2
  | tm_store t1 t2 t3 => locs_tm t1 ∪ locs_tm t2 ∪ locs_tm t3
  end.

Global Instance location_tm : Location tm := locs_tm.

Definition locs_ctx (k:ctx) : gset loc :=
  match k with
  | ctx_let _ t2 => locs_tm t2
  | ctx_call1 xs => ⋃ (locs_val <$> xs)
  | ctx_call2 t1 xs ys => locs_tm t1 ∪ ⋃ (locs_val <$> xs) ∪ ⋃ (locs_tm <$> ys)
  | ctx_bin_op1 _ t2 => locs_tm t2
  | ctx_bin_op2 _ v => locs_val v
  | ctx_if t2 t3 => locs_tm t2 ∪ locs_tm t3
  | ctx_alloc => ∅
  | ctx_load1 t2 => locs_tm t2
  | ctx_load2 v => locs_val v
  | ctx_store1 t1 t2 => locs_tm t1 ∪ locs_tm t2
  | ctx_store2 v t2 => locs_val v ∪ locs_tm t2
  | ctx_store3 v1 v2 => locs_val v1 ∪ locs_val v2
  end.

Global Instance location_ctx : Location ctx := locs_ctx.

Lemma locs_to_val t v :
  to_val t = Some v ->
  locs t = locs v.
Proof.
  intros E.
  destruct t; simpl in E; try congruence.
  injection E. intros ->.
  easy.
Qed.

Lemma locs_fmap_vals (vs:list val) :
  ⋃ (locs_tm <$> (tm_val <$> vs))%stdpp = locs vs.
Proof.
  induction vs; set_solver.
Qed.

Lemma locs_fill_item E t :
  locs (fill_item E t) = locs E ∪ locs t.
Proof.
  destruct E; try set_solver;
    unfold locs, location_tm; simpl.
  { rewrite locs_fmap_vals. set_solver. }
  rewrite fmap_app, fmap_cons.
  rewrite union_list_app_L, union_list_cons.
  rewrite locs_fmap_vals.
  set_solver.
Qed.

Ltac auto_locs :=
  unfold locs, location_list, location_ctx, location_tm, location_val, locs_list in *;
  simpl;
  rewrite ?locs_fill_item, ?locs_fmap_vals;
  auto_locs_val.

Lemma locs_elem_subseteq bs n v:
  bs !! n = Some v ->
  locs_val v ⊆ locs bs.
Proof.
  intros Hn.
  auto_locs. unfold location_list, locs_list.
  rewrite <- (take_drop_middle _ _ _ Hn).
  rewrite fmap_app, fmap_cons, union_list_app.
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* A simple helper *)

Definition is_loc v :=
  match v with
  | val_loc _ => true
  | _ => false end.

Lemma locs_val_no_loc v :
  ¬ is_loc v -> locs_val v = ∅.
Proof. destruct v; auto_locs; easy. Qed.

Lemma locs_no_loc v :
  ¬ is_loc v -> locs v = ∅.
Proof. intros. auto_locs. rewrite locs_val_no_loc; easy. Qed.
