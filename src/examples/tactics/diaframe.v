From spacelambda Require Import notation.
From spacelambda Require Import interp triple.
From spacelambda Require Import more_space_lang wp_all.
From spacelambda Require Import wp_spec wps.
From spacelambda Require Import qz smultiset.

From diaframe Require Import pure_solver.
From diaframe Require Export proofmode_base.

(* TODO:
   * Implement old tactics with diaframe.
   * Solve wpc issue.
   * Alloc?
 *)

(* ------------------------------------------------------------------------ *)
(* We extend the pure solver to call set_solver on goals requiring to prove
   the equality of sets. *)

(******************************************************************************)
(* Rewriting sets *)

(* Using rewrite to solve typeclasses instances. Maybe defining a set of lemmas
   already proving the right instances is more efficient *)
Ltac rew_map_set_step tt :=
  first [ rewrite left_id_L | rewrite right_id_L
        | rewrite difference_empty_L].

Ltac rew_set_core tt :=
  repeat (rew_map_set_step tt).

Tactic Notation "rew_set" := rew_set_core tt.

#[export] Hint Rewrite call_clo_eq : rewrite_llocs_tm.

(* this auto_locs focus only on the goal. *)
Ltac auto_locs_goal :=
  unfold locs, location_list, location_ctx, location_tm, location_val, locs_list;
  simpl;
  rewrite ?locs_fill_item ?locs_fmap_vals ?locs_mk_clo;
  repeat auto_locs_val;
  rew_set_core tt.

Ltac simpl_locs :=
  autorewrite with rewrite_llocs_tm;
  auto_locs_goal.

Ltac solve_locs :=
  match goal with
  | |- @eq (gset _) _ _ => simpl_locs; set_solver
  | |- @subseteq (gset _) _ _ => simpl_locs; set_solver end.

Global Hint Extern 4 (SolveSepSideCondition ?φ) => unfold SolveSepSideCondition; trySolvePure; solve_locs : typeclass_instances.

Section Diaframe.

Context `{hi:!interpGS Σ}.

(* ------------------------------------------------------------------------ *)
(* Wpc -> Wp *)

Definition is_val t : bool :=
  match t with
  | tm_val _ => true
  | _ => false end.

Definition to_val_force t : val :=
  match t with
  | tm_val v => v
  | _ => val_unit end.

Lemma fmap_to_val_force ts :
  forallb is_val ts →
  tm_val <$> (to_val_force <$> ts) = ts.
Proof.
  intros.
  induction ts as [|t ts]; try easy.
  do 2 rewrite fmap_cons.
  destruct t; simpl in *; try easy.
  f_equal. eauto.
Qed.

Lemma wps_call_tac `{!Enc A} X t self args body ts (Q:A -> iProp Σ) :
  t =(val_code self args body) ->
  forallb is_val ts →
  length args = length ts →
  locs body = ∅ →
  wps X (substs' (zip (self :: args) (t :: (to_val_force <$> ts))) body) Q -∗
  wps X (tm_call t ts) Q.
Proof.
  iIntros. subst.
  iApply (wps_call with "[$]"); eauto.
  { rewrite fmap_length //. }
  { rewrite fmap_to_val_force //. }
Qed.

Global Instance wp_call_instance `{!Enc A} X self args body ts (Φ:A -> iProp Σ) :
  SolveSepSideCondition (locs body = ∅) ->
  HINT1 empty_hyp_first ✱ [⌜forallb is_val ts = true⌝ ∗ ⌜length args = length ts⌝ ∗ wps X (substs' (zip (self :: args) ((val_code self args body) :: (to_val_force <$> ts))) body) Φ] ⊫ [id]; wps X (tm_call (val_code self args body) ts) Φ.
Proof.
  intros.
  iStepsS.
  iApply (wps_call_tac with "[$]"); eauto.
Qed.

Lemma wps_call_prim_tac `{!Enc A} X t p ts w (Q:A -> iProp Σ) :
  t = (val_prim p) ->
  forallb is_val ts →
  eval_call_prim p (to_val_force <$> ts) = Some (enc w) ->
  Q w -∗
  wps X (tm_call t ts) Q.
Proof.
  iIntros. subst.
  iApply (wps_mono with "[]").
  iApply wps_call_prim; eauto.
  { rewrite fmap_to_val_force //. }
  iIntros. subst. iFrame.
Qed.

Global Instance wp_call_prim_instance `{!Enc A} X (p:prim) ts (Φ:A -> iProp Σ) :
  SolveSepSideCondition (forallb is_val ts = true) ->
  HINT1 empty_hyp_first ✱ [∃ w, ⌜eval_call_prim p (to_val_force <$> ts) = Some (enc w)⌝ ∗ Φ w] ⊫ [id]; wps X (tm_call p ts) Φ.
Proof.
  intros.
  iStepsS.
  iApply wps_call_prim_tac; eauto.
Qed.

Lemma locs_to_val_force v :
  is_val v = true ->
  locs (to_val_force v) = locs v.
Proof.
  destruct v; set_solver.
Qed.

Lemma fmap_to_val_force_locs vs :
   forallb is_val vs ->
   locs (to_val_force <$> vs) = locs vs.
Proof.
  intros Hvs.
  induction vs as [|v]; try easy.
  auto_locs. simpl in *.
  rewrite locs_to_val_force.
  set_solver. destruct (is_val v); easy.
Qed.

Lemma wps_call_spec_tac `{Enc A} vs X n env P l (Ψ: A -> iProp Σ) :
  forallb is_val vs ->
  length vs = n ->
  Spec n env P l ∗
  (∀ t, P l (to_val_force <$> vs) t (Spec n env P l) -∗ wps X t Ψ) -∗
  wps X (call_clo l vs) Ψ.
Proof.
  iIntros (? ?) "(? & ?)".
  iApply (wps_call_spec with "[$]"); last iFrame.
  { rewrite fmap_to_val_force //. }
  { rewrite fmap_length //. }
Qed.

Global Instance call_spec_instance `{Enc A} vs X n env P (l:loc) (Ψ: A -> iProp Σ) :
  HINT1 empty_hyp_first ✱ [⌜forallb is_val vs⌝ ∗ ⌜length vs = n⌝ ∗ Spec n env P l ∗ (∀ t, P l (to_val_force <$> vs) t (Spec n env P l) -∗ wps X t Ψ)] ⊫ [id];  wps X (call_clo l vs) Ψ.
Proof.
  intros.
  iStepS.
  iApply (wps_call_spec_tac vs _ _ env P); eauto.
  iFrame.
Qed.

Global Instance bind_wps_None_instance `{!Enc A}  x t1 t2 (Φ:A -> iProp Σ) :
  HINT1 empty_hyp_first ✱ [wps None t1 (fun v => wps None (subst' x v t2) Φ)] ⊫ [id]; wps None (tm_let x t1 t2) Φ.
Proof.
  intros. iStepsS.
  iApply (wps_let_nofree with "[$]"); eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Post *)

Global Instance val_instance (A:Type) (EA:Enc A) X (v:val) (Φ:A -> iProp Σ):
  HINT1 empty_hyp_first ✱ [post Φ v] ⊫ [id]; wps X v Φ.
Proof.
  iStepS.
  iApply wps_val.
  iFrame.
Qed.

Global Instance post_val_instance (v:val) (Φ:val -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ v] ⊫ [id]; post Φ v.
Proof.
  rewrite post_val. iStepsS.
Qed.
Global Instance post_nat_instance (v:nat) (Φ:nat -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ v] ⊫ [id]; post Φ v.
Proof.
  rewrite post_nat. iStepsS.
Qed.
Global Instance post_loc_instance (v:loc) (Φ:loc -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ v] ⊫ [id]; post Φ v.
Proof.
  rewrite post_loc. iStepsS.
Qed.
Global Instance post_unit_instance (Φ:unit -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ tt] ⊫ [id]; post Φ val_unit.
Proof.
  rewrite post_unit.
  iStepsS.
Qed.


Definition go_nat t :=
  match t with
  | tm_call (prim_nat_op _) _ | tm_val (val_nat _) => true
  | _ => false end.
Global Instance go_nat_instance_val X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_nat t) ->
  HINT1 empty_hyp_first ✱ [wps X t (fun (n:nat) => Φ (enc n))] ⊫ [id]; wps X t Φ.
Proof.
  intros.
  iStepsS.
  iApply (wps_mono_val with "[$]").
  eauto.
Qed.

Definition go_loc t :=
  match t with
  | tm_alloc _ | tm_val (val_loc _) => true
  | _ => false end.
Global Instance go_loc_instance_val X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_loc t) ->
  HINT1 empty_hyp_first ✱ [wps X t (fun (l:loc) => Φ (enc l))] ⊫ [id]; wps X t Φ.
Proof.
  intros.
  iStepsS.
  iApply (wps_mono_val with "[$]").
  eauto.
Qed.

Definition go_unit t :=
  match t with
  | tm_store _ _ _ | tm_val val_unit => true
  | _ => false end.
Global Instance go_unit_instance_val X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_unit t) ->
  HINT1 empty_hyp_first ✱ [wps X t (fun (_:unit) => Φ (enc tt))] ⊫ [id]; wps X t Φ.
Proof.
  intros.
  iStepsS.
  iApply (wps_mono_val with "[$]").
  eauto.
Qed.

Definition go_bool t :=
  match t with
  | tm_call prim_eq _ | tm_call (prim_bool_op1 _) _ | tm_call (prim_bool_op2 _) _ => true
  | _ => false end.
Global Instance go_bool_instance_val X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_bool t) ->
  HINT1 empty_hyp_first ✱ [wps X t (fun (b:bool) => Φ (enc b))] ⊫ [id]; wps X t Φ.
Proof.
  intros.
  iStepsS.
  iApply (wps_mono_val with "[$]").
  eauto.
Qed.


(* ------------------------------------------------------------------------ *)
(* Rules *)

Global Instance load_instance (A:Type) (EA:Enc A) X (l:loc) (n:nat) (Φ:A -> iProp Σ):
  HINT1 empty_hyp_first ✱ [∃ (q:Qp) (vs:list val) (a:A), l ↦{q} (BBlock vs) ∗ ⌜0 <= n < length vs⌝ ∗ ⌜(vs !!! n) = enc a⌝ ∗ (l ↦{q} (BBlock vs)  -∗ Φ a)] ⊫ [id]; wps X (tm_load l n) Φ.
Proof.
  iStepsS. subst.
  iApply wps_end_val.
  iApply (wps_mono with "[H1]").
  iApply wps_load.
  2:iFrame.
  lia.
  iStepsS.
Qed.

Global Instance store_instance1 X (l:loc) (n:nat) (v:val) (Φ:unit -> iProp Σ):
  SolveSepSideCondition (is_loc v = false) ->
  HINT1 empty_hyp_first ✱
    [∃vs, l ↦ (BBlock vs) ∗ ⌜n < length vs⌝ ∗
         (∀ ret, (l ↦ (BBlock (<[n:=v]> vs))
            ∗ (vs !!! n)↤?{0}({[-l-]})) -∗ Φ ret) ] ⊫ [id]; wps X (tm_store l n v) Φ | 50.
Proof.
  intros.
  iStepsS.
  iApply (wps_mono with "[H1]").
  iApply (wps_store _ _ _ _ 1 ∅); last iFrame; eauto.
  lia. destruct v; try easy.
  iStepsS.
Qed.

Global Instance store_instance2 X (l:loc) (n:nat) (v:val) (Φ:unit -> iProp Σ):
  HINT1 empty_hyp_last ✱
    [∃vs qv lsv, l ↦ (BBlock vs) ∗ ⌜n < length vs⌝ ∗ v ↤?{qv} lsv ∗ ⌜is_loc v -> qv ≠ 0%Qz⌝ ∗
         (∀ ret, (l ↦ (BBlock (<[n:=v]> vs))
            ∗ v↤?{qv}(lsv ⊎ {[+ l +]})
            ∗ (vs !!! n)↤?{0}({[-l-]})) -∗ Φ ret) ] ⊫ [id]; wps X (tm_store l n v) Φ | 80.
Proof.
  iStepsS.
  iApply (wps_mono with "[H1 H2]").
  iApply wps_store; last iFrame; eauto.
  lia.
  iStepsS.
Qed.

Lemma wps_alloc_split n (m:Qz) X :
  Qz_le (nat_to_Qz n) m ->
  ♢ m -∗
  wps X (tm_alloc n)
  (fun (l:loc) =>
     ♢ (m - n) ∗
     l ↦ (BBlock (replicate n val_unit)) ∗
     l ↤ ∅ ∗
     Stackable l 1%Qp).
Proof.
  iIntros (?) "?".
  setoid_rewrite <- (Qz_sub_add m n) at 1; try easy.
  iDestruct (diamonds_split with "[$]") as "[H1 H2]".

  iApply (wps_mono with "[H2]").
  { iApply wps_alloc. eauto. }
  iIntros. iStepsS.
Qed.

Global Instance alloc_instance X (n:nat) (Φ:loc -> iProp Σ):
  HINT1 empty_hyp_first ✱ [∃m, ♢m ∗⌜Qz_le (nat_to_Qz n) m⌝ ∗ (∀ l, (♢ (m - n) ∗
           l ↦ (BBlock (replicate n val_unit)) ∗
           l ↤ ∅ ∗
           Stackable l 1%Qp) -∗ Φ l) ] ⊫ [id]; wps X (alloc n) Φ.
Proof.
  iStepS.
  iApply (wps_mono with "[H1]").
  iApply wps_alloc_split; last iFrame. easy.
  iStepsS.
Qed.

Global Instance mergable_consume_mapsto_own  l (q1 q2:Qz) (ls1 ls2:smultiset loc) :
  MergableConsume (l ↤{q1} ls1)%I (λ p Pin Pout,
      TCAnd (TCEq Pin (l ↤{q2} ls2)) $
(*        TCAnd (proofmode_classes.IsOp (A := gfracR) q q1 q2) $
        TCAnd (proofmode_classes.IsOp (A := smultisetR) ls ls1 ls2) $ *)
        (TCEq Pout (l ↤{q1 + q2} (ls1 ⊎ ls2))))%I | 30.
Proof.
  rewrite /MergableConsume => p Pin Pout [-> ->]. (* [+ [Hls +] ] ]. *)
  rewrite bi.intuitionistically_if_elim.
  iStartProof.
  iIntros "(H1 & ?)".
  iApply (mapsfrom_join with "[H1]"); iFrame.
Qed.
End Diaframe.

Global Opaque mapsfrom.
Global Opaque smultiset_equiv.
Global Opaque smultiset_disj_union.
