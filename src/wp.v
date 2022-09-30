From iris.proofmode Require Import base proofmode.
From iris.bi Require Import weakestpre.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import frac.

From spacelambda.language Require Import language.
From spacelambda Require Import more_maps_and_sets.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* Contexts. *)

Notation lctx := (gmap loc Qp).
Implicit Type k : lctx.

(* We explicit the merge of two contexts. *)
Definition kmerge k1 k2 :=
  map_union_with (λ a b, Some (a + b)%Qp) k1 k2.

(* It is indeed the cmra op. *)
Lemma kmerge_alt k1 k2 :
  kmerge k1 k2 = merge cmra.op k1 k2.
Proof. easy. Qed.

Lemma dom_kmerge k1 k2 : dom (kmerge k1 k2) = dom k1 ∪ dom k2.
Proof.
  by rewrite dom_map_union_with_full.
Qed.

(* ------------------------------------------------------------------------ *)
(* We define the WP w.r.t an abstract [interp] which is only required to
   satisfy some hypotheses described below.
*)

Definition nofree (r:gset loc) : gmap loc Qp :=
  gset_to_gmap 1%Qp r.

Lemma dom_nofree r : dom (nofree r) = r.
Proof. apply dom_gset_to_gmap. Qed.

Class spacelambdaGS (Σ : gFunctors) :=
  SpaceLambdaGS {
      iinvgs :> invGS Σ;
      (* A store interpretation predicate.
         [interp ctx σ roots] *)
      interp : bool -> nat -> lctx -> store -> gset loc -> iProp Σ;
      (* A predicate to say "not in the context" *)
      Stackables : gmap loc Qp -> iProp Σ;
      (* You can add roots to the context, provided they are not in it *)
      interp_shift : forall b maxsize k σ l1 L2 l2,
        l2 = dom L2 ->
        (interp b maxsize k σ (l1 ∪ l2) ∗ Stackables L2 ⊢ |==>
                (* l2 is now in the context *)
                (interp b maxsize (kmerge k L2) σ l1) ∗
                (* The capacity to restore the old context. *)
                (∀ σ' l1', ⌜dom σ ⊆ dom σ'⌝ -∗ interp b maxsize (kmerge k L2) σ' l1' ==∗
                            Stackables L2 ∗ interp b maxsize k σ' (l1' ∪ l2)));
      (* At any moment we can go _nofree_, with the mode set to false.
         If we give back this state, we can recover a mode were free is admissible. *)
      interp_nofree : forall maxsize k σ l,
        interp true maxsize k σ l ⊢
          interp false maxsize k σ l ∗
          (∀ σ' (l':gset loc), interp false maxsize k σ' l' -∗ interp true maxsize k σ' l');
      (* We can shift in the nofree mode. *)
      interp_shift_nofree : forall maxsize k σ l1 l2,
        (interp false maxsize k σ (l1 ∪ l2) ⊢ |==>
           (interp false maxsize (kmerge k (nofree l2)) σ l1) ∗
           (∀ σ' l1', ⌜dom σ ⊆ dom σ'⌝ -∗ interp false maxsize (kmerge k (nofree l2)) σ' l1' ==∗ interp false maxsize k σ' (l1' ∪ l2)));
      (* We can always weaken the roots. *)
      interp_weak : forall b maxsize l1 l2 k σ,
        l1 ⊆ l2 ->
        interp b maxsize k σ l2 ⊢ interp b maxsize k σ l1;
      (* The interpretation is stable by gc. *)
      interp_gc : forall b maxsize σ σ' k l,
        gc (dom k∪l) σ σ' ->
        interp b maxsize k σ l ⊢ interp b maxsize k σ' l;
    }.

Section wp.
Context `{!spacelambdaGS Σ}.

(* ------------------------------------------------------------------------ *)
(* The actual wp. *)

(* We require [interp maxsize k σ t] even in the case of a value, because we want to
   be able to do a free even we looking at a value *)

Definition wp_pre (b:bool)
  (wp : tm -d> (val -d> iPropO Σ) -d> iPropO Σ) :
  tm -d> (val -d> iPropO Σ) -d> iPropO Σ := λ t Q,
  (∀ maxsize k σ, interp b maxsize k σ (locs t) ==∗
  match to_val t with
  | Some v => (interp b maxsize k σ (locs t) ∗ Q v)
  | None =>
       ⌜reducible maxsize (dom k) t σ⌝ ∗
       ▷ (∀ t' σ', ⌜alt_reduction maxsize (dom k) t σ t' σ'⌝ ==∗
       (interp b maxsize k σ' (locs t') ∗ wp t' Q))
  end)%I.

Local Instance wp_pre_contractive b : Contractive (wp_pre b).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp t Q.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

(* wp as the fixpoint of wp_pre *)
Definition wp b : tm -> (val -> iProp Σ) -> iProp Σ :=
  fixpoint (wp_pre b).

Lemma wp_unfold b t Q :
  wp b t Q ⊣⊢ wp_pre b (wp b) t Q.
Proof. apply (fixpoint_unfold (wp_pre b)). Qed.

Global Instance wp_ne b t n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp b t).
Proof.
  revert t. induction (lt_wf n) as [n _ IH]=> t Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 18 (f_contractive || f_equiv).
  apply IH. lia.
  intros v. eapply dist_S, HΦ.
Qed.

Global Instance wp_contractive b t n :
  (to_val t) = None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp b t).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  repeat (f_contractive || f_equiv).
Qed.

(* ------------------------------------------------------------------------ *)
(* Usual properties of wp. *)

Lemma wp_strong_mono b t Q Q' :
  wp b t Q -∗ (∀ v, Q v ==∗ Q' v) -∗ wp b t Q'.
Proof.
  iIntros "H HQ".
  iLöb as "IH" forall (t Q Q').
  rewrite !wp_unfold /wp_pre /=.
  iIntros (? k σ) "Hσ".
  destruct (to_val t) as [v|] eqn:?.
  { iMod ("H" with "[$]") as "[? ?]".
    iFrame. by iApply "HQ". }
  { iMod ("H" with "[$]") as "[%Hr H]".
    iModIntro.
    iSplitR.
    { by iPureIntro. }
    iIntros (t' σ' Hstep).
    iModIntro. iMod ("H" with "[% //]") as "[? H]".
    iModIntro. iFrame.
    by iApply ("IH" with "H"). }
Qed.

Lemma wp_mono b t Q Q' :
  wp b t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wp b t Q'.
Proof.
  iIntros "? H".
  iApply (wp_strong_mono with "[$]").
  iIntros. by iApply "H".
Qed.

Lemma wp_bupd b t Q :
  (|==> wp b t Q) ⊢ wp b t Q.
Proof.
  iIntros "Hwp".
  rewrite wp_unfold /wp_pre.
  destruct (to_val t);
     iMod "Hwp"; iFrame.
Qed.

Lemma wp_frame b t Φ Ψ :
  Φ ∗ wp b t Ψ ⊢ wp b t (fun v => Φ ∗ Ψ v).
Proof.
  iIntros "[? Hwp]".
  iApply (wp_strong_mono with "Hwp").
  eauto with iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* Properties of wp on the language. *)

Lemma wp_val b v Q :
  Q v ⊢ wp b (tm_val v) Q.
Proof.
  iIntros.
  rewrite wp_unfold.
  iFrame. iIntros. by iFrame.
Qed.

(* A lemma for adding a wp on the last value. This enable access to the state_interp
   at the last step *)
Lemma wp_end b t Q :
  wp b t (fun v => wp b v Q) -∗
  wp b t Q.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (t Q).
  rewrite !wp_unfold /wp_pre /=.
  iIntros. iMod ("Hwp" with "[$]") as "Hwp".
  destruct (to_val t) eqn:E; iIntros.
  { iDestruct "Hwp" as "(? & Hwp)".
    destruct t; try easy.
    injection E. intros. subst.
    rewrite wp_unfold /wp_pre. simpl.
    iMod ("Hwp" with "[$]") as "(? & ?)".
    by iFrame. }
  { iDestruct "Hwp" as "(? & Hwp)".
    iFrame. do 2 iModIntro.
    iIntros.
    iMod ("Hwp" with "[% //]") as "[? ?]".
    iModIntro.
    iFrame. iApply "IH". iFrame. }
Qed.

(* ------------------------------------------------------------------------ *)
(* supd allows a fancy update of P to Q under access to interp. *)

Definition supd b L P Q : Prop :=
  P -∗ ∀ maxsize k σ,
    interp b maxsize k σ L ==∗ interp b maxsize k σ L ∗ Q.

Local Notation "P =[ b | L ]=∗ Q" := (supd b L P Q)%I
 (at level 99, Q at level 200).

Lemma wp_conseq b P Q t φ :
  (P =[ b | locs t ]=∗ Q) ->
  (Q -∗ wp b t φ) -∗
  (P -∗ wp b t φ).
Proof.
  iIntros (Hs) "Hwp ?".
  rewrite wp_unfold.
  iIntros (? ? ?) "?".
  iMod (Hs with "[$] [$]") as "[? ?]".
  iApply ("Hwp" with "[$] [$]").
Qed.

Lemma supd_simpl b P Q V M :
  dom M ⊆ V ->
  (P =[ b | (V ∖ dom M) ]=∗ Q) ->
  (Stackables M ∗ P =[ b | V ]=∗ Stackables M ∗ Q).
Proof.
  iIntros (? HPQ).
  iIntros "(? & ?)".
  iIntros.
  replace V with ((V ∖ dom M) ∪ dom M).
  2:{ rewrite union_comm_L -union_difference_L //. }
  iMod (interp_shift with "[$]") as "(? & HK)"; first easy.
  iMod (HPQ with "[$] [$]") as "(? & ?)".
  iMod ("HK" with "[%] [$]") as "(? & ?)"; first set_solver.
  by iFrame.
Qed.

Lemma to_val_fill_item E t :
  to_val (fill_item E t) = None.
Proof. now destruct E. Qed.

Lemma wp_bind b E L t Q :
  locs E = dom L ->
  wp b t (fun v => Stackables L -∗ wp b (fill_item E v) Q) -∗
     Stackables L -∗ wp b (fill_item E t) Q.
Proof.
  iIntros (HL) "H Hctx". iLöb as "IH" forall (t). rewrite wp_unfold /wp_pre.
  destruct (to_val t) as [v|] eqn:Et.
  { iClear "IH".
    setoid_rewrite wp_unfold at 2. rewrite /wp_pre.
    destruct t; try easy. simpl.
    injection Et; intros ->.
    iIntros (? k σ) "Hσ".

    rewrite locs_fill_item union_comm_L.
    iDestruct (interp_shift with "[$]") as ">[Hσ Hback]".
    { easy. }

    iMod ("H" with "[$]") as "[? H]".
    iMod ("Hback" with "[%] [$]") as "[Hctx Hσ]".
    { easy. }

    iDestruct ("H" with "Hctx") as "H".
    rewrite wp_unfold /wp_pre.
    simpl. iFrame.
    rewrite locs_fill_item union_comm_L.
    iApply "H". iFrame. }
  { rewrite !wp_unfold /wp_pre. simpl.
    iIntros (? k σ) "Hσ".

    rewrite locs_fill_item union_comm_L.

    iDestruct (interp_shift with "[$]") as ">[Hσ Hback]".
    { easy. }

    iMod ("H" with "[$]") as "[%Hred H]".
    iModIntro.
    rewrite to_val_fill_item.
    iSplitR.
    { iPureIntro.
      rewrite dom_kmerge -HL in Hred.
      eauto using reducible_context. }
    iIntros (t' σ' Hstep).
    destruct (invert_step_context _ _ Et Hstep) as (t1',(?&Hstep')); subst.
    iModIntro. iMod ("H" with "[%]") as "[? Hwp]".
    { by rewrite dom_kmerge -HL. }
    iDestruct ("Hback" with "[%] [$]") as ">[Hctx Hσ]".
    { eauto using alt_reduction_grow_store. }
    iModIntro. rewrite locs_fill_item union_comm_L.
    iDestruct ("IH" with "Hwp Hctx") as "?". iFrame. }
Qed.

Lemma wp_nofree b t Q :
  wp false t Q -∗ wp b t Q.
Proof.
  destruct b; try easy.
  iIntros "Hwp".
  iLöb as "IH" forall (t Q).
  rewrite !wp_unfold /wp_pre /=.
  iIntros (? k σ) "Hσ".
  destruct (to_val t) as [v|] eqn:?.
  { iDestruct (interp_nofree with "[$]") as "(HL & HR)".
    iMod ("Hwp" with "[$]") as "(? & ?)". iModIntro.
    iFrame. iApply "HR". iFrame. }
  iDestruct (interp_nofree with "[$]") as "(HL & HR)".
  iMod ("Hwp" with "[$]") as "(? & Hback)". iModIntro.
  iFrame.
  iIntros. iModIntro. iIntros.
  iMod ("Hback" with "[% //]") as "(? & ?)". iModIntro.
  iSpecialize ("HR" with "[$]"). iFrame.
  iApply "IH". iFrame.
Qed.

Lemma wp_bind_nofree_false E t Q :
  wp false t (fun v =>  wp false (fill_item E v) Q) -∗
  wp false (fill_item E t) Q.
Proof.
  iIntros "Hwp". iLöb as "IH" forall (t). rewrite wp_unfold /wp_pre.
  destruct (to_val t) as [v|] eqn:Et.
  { iClear "IH".
    setoid_rewrite wp_unfold at 2. rewrite /wp_pre.
    destruct t; try easy. simpl.
    injection Et; intros ->.
    iIntros (? k σ) "Hσ".

    rewrite locs_fill_item union_comm_L.
    iDestruct (interp_shift_nofree with "[$]") as ">[Hσ Hback]".

    iMod ("Hwp" with "[$]") as "[? H]".
    iMod ("Hback" with "[% //] [$]").

    rewrite wp_unfold /wp_pre.
    simpl. iFrame.
    rewrite locs_fill_item union_comm_L.
    iApply "H". iFrame. }
  { rewrite !wp_unfold /wp_pre. simpl.
    iIntros (? k σ) "Hσ".

    rewrite locs_fill_item union_comm_L.

    iDestruct (interp_shift_nofree with "[$]") as ">[Hσ Hback]".

    iMod ("Hwp" with "[$]") as "[%Hred H]".
    iModIntro.
    rewrite to_val_fill_item.
    iSplitR.
    { iPureIntro.
      rewrite dom_kmerge dom_nofree in Hred.
      eauto using reducible_context. }
    iIntros (t' σ' Hstep).
    destruct (invert_step_context _ _ Et Hstep) as (t1',(?&Hstep')); subst.
    iModIntro. iMod ("H" with "[%]") as "[? Hwp]".
    { by rewrite dom_kmerge dom_nofree. }
    iMod ("Hback" with "[%] [$]").
    { eauto using alt_reduction_grow_store. }
    iModIntro. rewrite locs_fill_item union_comm_L.
    iDestruct ("IH" with "Hwp") as "?". iFrame. }
Qed.

Lemma wp_bind_nofree b E t Q :
  wp false t (fun v =>  wp b (fill_item E v) Q) -∗
  wp b (fill_item E t) Q.
Proof.
  iIntros "Hwp".
  destruct b; last first.
  { iApply wp_bind_nofree_false. iFrame. }
  iLöb as "IH" forall (t). rewrite wp_unfold /wp_pre.
  destruct (to_val t) as [v|] eqn:Et.
  { iClear "IH".
    setoid_rewrite wp_unfold at 2. rewrite /wp_pre.
    destruct t; try easy. simpl.
    injection Et; intros ->.
    iIntros (? k σ) "Hσ".
    rewrite locs_fill_item union_comm_L.
    iDestruct (interp_nofree with "[$]") as "(HL & HR)".
    iMod (interp_shift_nofree with "[$]") as "(? & Hback)".
    iMod ("Hwp" with "[$]") as "[? H]".
    iMod ("Hback" with "[% //] [$]").

    rewrite wp_unfold /wp_pre.
    simpl. iFrame.
    rewrite locs_fill_item union_comm_L.
    iApply "H". iApply "HR". iFrame. }
  { rewrite !wp_unfold /wp_pre. simpl.
    iIntros (? k σ) "Hσ".

    rewrite locs_fill_item union_comm_L.

    iDestruct (interp_nofree with "[$]") as "(HL & HR)".
    iMod (interp_shift_nofree with "[$]") as "(? & Hback)".
    iMod ("Hwp" with "[$]") as "[%Hred H]".
    iModIntro.
    rewrite to_val_fill_item.
    iSplitR.
    { iPureIntro.
      rewrite dom_kmerge dom_nofree in Hred.
      eauto using reducible_context. }
    iIntros (t' σ' Hstep).
    destruct (invert_step_context _ _ Et Hstep) as (t1',(?&Hstep')); subst.
    iModIntro.
    iMod ("H" with "[%]") as "[? Hwp]".
    { by rewrite dom_kmerge dom_nofree. }
    iMod ("Hback" with "[%] [$]").
    { eauto using alt_reduction_grow_store. }
    iModIntro. rewrite locs_fill_item union_comm_L.
    iDestruct ("IH" with "Hwp") as "?". iFrame.
    iApply "HR". iFrame. }
Qed.

Lemma wp_let_val b x (v:val) t Q :
  wp b (subst' x v t) Q -∗
  wp b (tm_let x v t) Q.
Proof.
  iIntros. setoid_rewrite wp_unfold at 2.
  iIntros (? ? ?) "?".
  iSplitR.
  { eauto using reducible_let_val. }
  iModIntro. iIntros (? ?) "%Hstep".
  apply invert_step_let_val in Hstep. destruct Hstep as (->&?).
  do 2 iModIntro. iFrame.
  iDestruct (interp_gc with "[$]") as "?".
  { auto_locs. eauto. }
  iApply (interp_weak with "[$]").
  destruct x; try set_solver.
  apply locs_subst.
Qed.

Lemma wp_let b L2 x t1 t2 Q :
  locs t2 = dom L2 ->
  wp b t1 (fun v => Stackables L2 -∗ wp b (subst' x v t2) Q) -∗
     Stackables L2  -∗ wp b (tm_let x t1 t2) Q.
Proof.
  intros. iIntros "H HL2".
  iApply (wp_bind b (ctx_let x t2) with "[H]").
  { auto_locs. eauto. }
  2:{ iFrame. }
  iApply (wp_mono with "[$]").
  iIntros (?) "Hwp ?". simpl.
  iApply wp_let_val. now iApply "Hwp".
Qed.

Lemma wp_let_nofree x t1 t2 b Q :
  wp false t1 (fun v => wp b (subst' x v t2) Q) -∗
  wp b (tm_let x t1 t2) Q.
Proof.
  intros. iIntros "H".
  iApply (wp_bind_nofree b (ctx_let x t2) with "[H]").
  iApply (wp_mono with "[$]").
  iIntros (?) "Hwp ". simpl.
  iApply wp_let_val. now iApply "Hwp".
Qed.

Lemma interp_gc_weak b maxsize k σ1 σ2 L1 L2 L3 :
  L1 ⊆ L2 ⊆ L3 ->
  gc (dom k ∪ L3) σ1 σ2 ->
  interp b maxsize k σ1 L2 ==∗
         interp b maxsize k σ2 L1.
Proof.
  iIntros (? Hgc) "?".
  iApply interp_gc.
  { apply (gc_weak Hgc).
    set_solver. }
  iApply interp_weak; try by iFrame.
  set_solver.
Qed.

Lemma wp_if_later b n t1 t2 Q :
   ▷ (if (decide (n ≠ 0)) then wp b t1 Q else wp b t2 Q)
    -∗ wp b (tm_if n t1 t2) Q.
Proof.
  iIntros "Hwp".
  iApply wp_unfold.
  unfold wp_pre. simpl.

  iIntros (? k σ) "Hi".

  iSplitR.
  { iPureIntro. apply reducible_if. }
  iModIntro.

  iIntros (t' σ') "%Hstep".
  apply invert_step_if in Hstep.
  destruct Hstep as (Hgc & Hif).
  rewrite -union_assoc_L in Hgc.
  iModIntro.
  destruct Hif as [(Hn&Ht1)|(Hn&Ht2)]; subst; simpl.
  { rewrite decide_True //. iFrame.
    iApply interp_gc_weak; try iFrame.
    2:{ apply Hgc. }
    set_solver. }
  { iFrame.
    iApply interp_gc_weak; try iFrame.
    2:{ apply Hgc. }
    set_solver. }
Qed.

Lemma wp_if b n t1 t2 Q :
  (if (decide (n ≠ 0)) then wp b t1 Q else wp b t2 Q)
  -∗ wp b (tm_if n t1 t2) Q.
Proof. iIntros. iApply wp_if_later. iModIntro. eauto. Qed.

End wp.

Notation "P =[ b | L ]=∗ Q" := (supd b L P Q)%I
 (at level 99, Q at level 200).
