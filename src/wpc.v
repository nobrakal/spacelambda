From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.
From spacelambda Require Import more_space_lang more_maps_and_sets.
From spacelambda Require Import interp.

From spacelambda Require Import wp_alloc wp_call wp_load wp_bin_op wp_store wp_spec.
From spacelambda Require Export wp_enc.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* kdiv: divide a context by 2. *)

Definition kdiv (k:lctx) : lctx :=
  fmap (fun q => (q/2)%Qp) k.

Lemma dom_kdiv k : dom (kdiv k) = dom k.
Proof.
  unfold kdiv.
  apply leibniz_equiv.
  by rewrite dom_fmap.
Qed.

(* A context is the union of its two halves. *)
Lemma kdiv_both (k:lctx) :
  k = kmerge (kdiv k) (kdiv k).
Proof.
  unfold kmerge,kdiv.
  apply leibniz_equiv.
  intros x.
  rewrite lookup_union_with.
  rewrite lookup_fmap.
  destruct (k !! x) eqn:E; rewrite E; simpl; try easy.
  by rewrite Qp_div_2.
Qed.

Section Wpc.

Context `{!interpGS Σ}.

Lemma Stackables_kmerge k1 k2 :
  Stackables (kmerge k1 k2) ≡ (Stackables k1 ∗ Stackables k2)%I.
Proof.
  unfold Stackables.
  rewrite auth_frag_op.
  by rewrite own_op.
Qed.

Lemma Stackables_kdiv k :
  Stackables k ⊣⊢ Stackables (kdiv k) ∗ Stackables (kdiv k).
Proof.
  setoid_rewrite (kdiv_both k) at 1.
  by rewrite Stackables_kmerge.
Qed.

(* ------------------------------------------------------------------------ *)
(* A wp_let approx *)


Lemma split_map (k:lctx) (d:gset loc) :
  d ⊆ dom k ->
  k = kmerge (restrict k d) (restrict k (dom k ∖ d)).
Proof.
  intros.
  apply leibniz_equiv.
  intros x.
  rewrite lookup_union_with.
  do 2 rewrite lookup_restrict.
  destruct (decide (x ∈ d)).
  { destruct (decide (x ∈ dom k ∖ d)).
    { exfalso. set_solver. }
    { by rewrite right_id_L. } }
  { rewrite left_id_L.
    destruct (decide (x ∈ dom k ∖ d)); try easy.
    destruct (decide (x ∈ k)).
    { exfalso. set_solver. }
    { destruct (k !! x) eqn:E; rewrite E; try easy.
      apply lookup_Some_in_dom in E.
      set_solver. } }
Qed.

Lemma wp_let_approx L2 x t1 t2 b Q :
  locs t2 ⊆ dom L2 ->
  wp b t1 (fun v => Stackables L2 -∗ wp b (subst' x v t2) Q) -∗
  Stackables L2  -∗ wp b (tm_let x t1 t2) Q.
Proof.
  iIntros (Hincl) "? ?".
  rewrite (split_map Hincl).
  rewrite kmerge_alt. iDestruct (Stackables_split with "[$]") as "[Hl ?]".
  iApply (wp_let with "[-Hl]").
  3:{ iFrame. }
  { rewrite dom_restrict. set_solver. }
  iApply (wp_mono with "[$]"). iIntros (?) "Hkont ?".
  iDestruct (Stackables_kmerge with "[$]") as "?".
  iApply "Hkont". iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* wpc *)

(* A wp with context: it is a kind of frame of a context, with memory. *)
Definition wpc `{Enc A} (r:gset loc) (t:tm) (Q:A -> iProp Σ) :=
  (∀ (k:lctx), ⌜r ⊆ dom k⌝ -∗
  Stackables k -∗ wp_enc true t (fun a => (Stackables k ∗ Q a)))%I.

Global Instance wpc_ne `{!interpGS Σ} A (HA:Enc A) r t n :
  Proper (pointwise_relation A (dist n) ==> dist n) (wpc r t).
Proof.
  revert t. induction (lt_wf n) as [n _ IH]=> t Φ Ψ HΦ.
  unfold wpc,post,wpc.
  repeat (f_contractive || f_equiv).
Qed.

(* We inherit strong mono. *)
Lemma wpc_strong_mono (A:Type) (EA:Enc A) r t (Q Q':A -> iProp Σ) :
  wpc r t Q -∗ (∀ v, Q v ==∗ Q' v) -∗ wpc r t Q'.
Proof.
  iIntros "Hwpc HQQ'".
  iIntros (k) "? ?".
  iSpecialize ("Hwpc" with "[$] [$]").
  iApply (wp_enc_strong_mono with "[$]").
  iIntros (?) "[? ?]".
  iFrame.
  by iApply "HQQ'".
Qed.

Lemma wpc_mono (A:Type) (EA:Enc A) r t (Q Q':A -> iProp Σ) :
  wpc r t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wpc r t Q'.
Proof.
  iIntros "? H".
  iApply (wpc_strong_mono with "[$]").
  iIntros. by iApply "H".
Qed.

Lemma wpc_mono_val (A:Type) (EA:Enc A) r t (Q:A -> iProp Σ) (Q':val -> iProp Σ) :
  wpc r t Q -∗ (∀ v, Q v -∗ Q' (enc v)) -∗ wpc r t Q'.
Proof.
  iIntros "Hwp Hq".
  iIntros (?) "%Hk ?".
  iSpecialize ("Hwp" with "[%//] [$]").
  iApply (wp_enc_mono_val with "[$]").
  iIntros (?) "(? & ?)". iFrame.
  iApply "Hq". iFrame.
Qed.

Lemma wpc_bupd (A:Type) (EA:Enc A) r t (Q:A -> iProp Σ) :
  (|==> wpc r t Q) ⊢ wpc r t Q.
Proof.
  iIntros "Hwpc".
  iIntros (?) "? ?".
  iApply wp_enc_bupd.
  iMod "Hwpc". iModIntro.
  iApply ("Hwpc" with "[$] [$]").
Qed.

(* We can prove wpc from any wp, thanks to frame. *)
Lemma wp_wpc (A:Type) (EA:Enc A) r t (Q:A -> iProp Σ) :
  wp_enc true t Q ⊢ wpc r t Q.
Proof.
  iIntros "?".
  iIntros (? ?) "?".
  iApply (wp_enc_mono with "[$]").
  iIntros. iFrame.
Qed.

(* To prove a wp, we can prove a wpc with an empty context. *)
Lemma wpc_wp_empty (A:Type) (EA:Enc A) t (Q:A -> iProp Σ) :
  wpc ∅ t Q ⊢ wp_enc true t Q.
Proof.
  iIntros "Hwpc".
  iApply wp_enc_bupd.
  iAssert (|==> Stackables ∅)%I as ">?".
  { iApply own_unit. }
  iModIntro.
  iSpecialize ("Hwpc" with "[%] [$]").
  { by rewrite dom_empty_L. }
  iApply (wp_enc_strong_mono with "[$]"); try iFrame.
  iIntros (?) "[? ?]".
  by iFrame.
Qed.

(* We can "frame" a context, and remember it. *)
Lemma wpc_extend (A:Type) (EA:Enc A) r2 r1 k t (Q:A -> iProp Σ) :
  r2 = dom k ->
  Stackables k ∗ wpc (r2 ∪ r1) t Q ⊢ wpc r1 t (fun v => Stackables k ∗ Q v).
Proof.
  iIntros (?) "[? Hwpc]".
  iIntros (k1 Hk1) "?".
  iAssert (Stackables k ∗ Stackables k1)%I with "[$]" as "?".
  rewrite -Stackables_kmerge.
  iSpecialize ("Hwpc" with "[%] [$]").
  { rewrite dom_kmerge. set_solver. }
  iApply (wp_enc_strong_mono with "[$]").
  iIntros (?).
  rewrite Stackables_kmerge.
  iIntros "[[? ?] ?]".
  by iFrame.
Qed.

Lemma wpc_context (A:Type) (EA:Enc A) r' r t Q :
  Stackables r' ∗ wpc (dom r' ∪ r) t (fun v:A => Stackables r' -∗ Q v) -∗
  wpc r t Q.
Proof.
  iIntros.
  iDestruct (wpc_extend with "[$]") as "?"; try easy.
  iApply (wpc_mono with "[$]").
  iIntros (?) "[? Hp]".
  iApply "Hp". eauto.
Qed.

Lemma wpc_context_singleton l q r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  Stackable l q ∗ wpc ({[l]} ∪ r) t (fun v:A => Stackable l q -∗ Q v) -∗
  wpc r t Q.
Proof.
  iIntros "[Hlq ?]".
  iApply (wpc_context {[l:=q]}).
  iFrame "Hlq". rewrite dom_singleton_L. iFrame.
Qed.

Lemma wpc_weak (A:Type) (EA:Enc A) r1 r2 t (Q:A -> iProp Σ) :
  r1 ⊆ r2 ->
  wpc r1 t Q -∗ wpc r2 t Q.
Proof.
  iIntros (?) "Hwpc".
  iIntros (? ?) "?".
  iApply ("Hwpc" with "[%] [$]").
  set_solver.
Qed.

Lemma wpc_wp (A:Type) (EA:Enc A) r k t (Q:A -> iProp Σ) :
  r = dom k ->
  Stackables k ∗ wpc r t Q ⊢ wp_enc true t (fun v => Stackables k ∗ Q v).
Proof.
  iIntros (?) "[? Hwpc]".
  iApply wpc_wp_empty.
  iApply wpc_extend; try easy.
  rewrite right_id_L. subst.
  iFrame.
Qed.

Lemma wpc_bind (A:Type) (EA:Enc A) r E t k (Q:A -> iProp Σ) :
  (locs E) ⊆ r ∪ (dom k) ->
  Stackables k -∗
  wpc (r ∪ locs E) t (fun (v:val) => Stackables k -∗ wpc r (fill_item E v) Q) -∗
  wpc r (fill_item E t) Q.
Proof.
  iIntros (?) "Hk Hwpc".
  iIntros (k' Hrk') "Hk'".

  iDestruct (Stackables_kdiv with "Hk") as "[Hk1 Hk2]".
  iDestruct (Stackables_kdiv with "Hk'") as "[Hk'1 Hk'2]".
  iDestruct (Stackables_kmerge with "[Hk'1 Hk1]") as "H1"; try iFrame.
  iDestruct (Stackables_kmerge with "[Hk'2 Hk2]") as "H2"; try iFrame.

  iSpecialize ("Hwpc" with "[%] [$]"); try iFrame.
  { rewrite dom_kmerge.
    do 2 rewrite dom_kdiv.
    set_solver. }

  assert (locs E ⊆ dom (kmerge (kdiv k) (kdiv k'))).
  { rewrite dom_kmerge. do 2 rewrite dom_kdiv. set_solver. }


  rewrite (@split_map (kmerge (kdiv k) (kdiv k')) (locs E)); last easy.
  iDestruct (Stackables_kmerge with "H1") as "[? Hl]".

  iApply (wp_enc_bind with "[Hwpc Hl]"); try iFrame.
  { rewrite dom_restrict.
    rewrite dom_kmerge.
    do 2 rewrite dom_kdiv.
    set_solver. }
  iApply (@wp_enc_strong_mono with "[$]"); try iFrame.
  iIntros (v) "[Hkk1 Hwpc]".
  iModIntro. iIntros "Hkk2". simpl.

  iDestruct (own_op with "[Hl Hkk2]") as "Hkk2"; try iFrame.
  rewrite -auth_frag_op.

  unfold op, cmra_op. simpl. unfold ucmra_op. simpl.
  unfold gmap_op_instance.
  rewrite -kmerge_alt.

  rewrite -split_map; last easy.

  iDestruct (Stackables_kmerge with "Hkk1") as "[? ?]".
  iDestruct (Stackables_kmerge with "Hkk2") as "[? ?]".
  iDestruct (Stackables_kdiv with "[$]") as "?".
  iDestruct (Stackables_kdiv with "[$]") as "?".

  iApply ("Hwpc" with "[$] [% //] [$]").
Qed.

Lemma wpc_bind_nofree (A:Type) (EA:Enc A) r E t (Q:A -> iProp Σ) :
  wp_enc false t (fun (v:val) => wpc r (fill_item E v) Q) -∗
  wpc r (fill_item E t) Q.
Proof.
  iIntros.
  iIntros (?) "? ?".
  iApply wp_enc_bind_nofree.
  iApply (wp_enc_mono with "[$]").
  iIntros (?) "Hwp".
  iApply ("Hwp" with "[$] [$]").
Qed.

Ltac start_deriv str :=
  iIntros str;
  iIntros (k) "%Hk Hnctx".

Lemma wpc_let_val (A:Type) (EA:Enc A) r x (v:val) t (Q:A -> iProp Σ) :
  wpc r (subst' x v t) Q -∗
  wpc r (tm_let x v t) Q.
Proof.
  start_deriv "Hwp".
  rewrite wp_enc_eq.
  iApply wp_let_val.
  iApply ("Hwp" with "[% //] [$]").
Qed.

Lemma wpc_let (A:Type) (EA:Enc A) r x t1 t2 k (Q:A -> iProp Σ) :
  (locs t2) ⊆ r ∪ (dom k) ->
  Stackables k  -∗
  wpc (r ∪ locs t2) t1 (fun v => Stackables k -∗ wpc r (subst' x v t2) Q) -∗
  wpc r (tm_let x t1 t2) Q.
Proof.
  iIntros (?) "H ?".
  iApply (wpc_bind _ _ (ctx_let x t2) with "[H]").
  { auto_locs. eauto. }
  { iFrame. }
  auto_locs.
  iApply (@wpc_mono with "[$]").
  iIntros (?) "Hwp ?". simpl.
  iApply wpc_let_val.
  iApply "Hwp".
  iFrame.
Qed.

Lemma wpc_let_nofree (A:Type) (EA:Enc A) r x t1 t2 (Q:A -> iProp Σ) :
  wp_enc false t1 (fun v => wpc r (subst' x v t2) Q) -∗
  wpc r (tm_let x t1 t2) Q.
Proof.
  iIntros.
  iApply (wpc_bind_nofree _ _ (ctx_let x t2)).
  iApply (wp_enc_mono with "[$]").
  iIntros (?) "Hwp". simpl.
  iApply wpc_let_val.
  iApply "Hwp".
Qed.

Lemma wpc_if (A:Type) (EA:Enc A) r n t1 t2 (Q:A -> iProp Σ) :
  (if (decide (n ≠ 0)) then wpc r t1 Q else wpc r t2 Q)
    ⊢ wpc r (tm_if n t1 t2) Q.
Proof.
  start_deriv "Hwpc".
  iApply @wp_enc_if.
  case_decide; iApply "Hwpc"; eauto.
Qed.

Lemma wpc_call (A:Type) (EA:Enc A) r self args body vs ts (Q:A -> iProp Σ) :
  length args = length vs →
  locs body = ∅ →
  ts = tm_val <$> vs →
  wpc r (substs' (zip (self :: args) (val_code self args body :: vs)) body) Q -∗
     wpc r (tm_call (val_code self args body) ts) Q.
Proof.
  intros.
  start_deriv "Hwpc".
  iSpecialize ("Hwpc" $! k with "[% //] Hnctx").
  iApply (@wp_enc_strong_mono with "[Hwpc]").
  { iApply wp_enc_call; eauto. }
  eauto.
Qed.

Lemma wpc_call_spec (A:Type) (EA:Enc A) P (vals:list val) r n env l  vs (Ψ: A -> iProp Σ) :
  vs = (tm_val <$> vals) ->
  length vals = n ->
  Spec n env P l -∗
  (∀ t, P l vals t (Spec n env P l) -∗ wpc r t Ψ) -∗
  wpc r (call_clo l vs) Ψ.
Proof.
  iIntros (? ?) "? Hwpc".
  iIntros (?) "%Hk ?".
  iApply (wp_enc_call_spec with "[$]"); eauto.
  iIntros.
  iApply ("Hwpc" with "[$]"); eauto.
Qed.

Lemma wpc_val (A:Type) (EA:Enc A) r (v:A) (Q:A -> iProp Σ) :
  Q v -∗
  wpc r (enc v) Q.
Proof.
  start_deriv "Hwpc".
  rewrite wp_enc_eq.
  iApply @wp_val.
  iFrame. iExists _. iFrame. eauto.
Qed.

Lemma wpc_end (A:Type) (EA:Enc A) r t (Q:A -> iProp Σ) :
  wpc r t (fun a  => wpc r (enc a) Q) -∗
  wpc r t Q.
Proof.
  start_deriv "Hwpc".
  iSpecialize ("Hwpc" $! k with "[% //] Hnctx").
  iApply @wp_enc_end.
  iApply (@wp_enc_mono with "[$]").
  iIntros (?) "(? & Hwpc)".
  iSpecialize ("Hwpc" $! k with "[% //] [$]").
  eauto.
Qed.

Lemma wpc_end_val (A:Type) (EA:Enc A) r t (Q:A -> iProp Σ) :
  wpc r t (fun (v:val) => wpc r v Q) -∗
  wpc r t Q.
Proof.
  start_deriv "Hwpc".
  iSpecialize ("Hwpc" $! k with "[% //] Hnctx").
  iApply @wp_enc_end_val.
  iApply (@wp_enc_mono with "[$]").
  iIntros (?) "(? & Hwpc)".
  iSpecialize ("Hwpc" $! k with "[% //] [$]").
  eauto.
Qed.

End Wpc.

Section Supd.

Context `{!interpGS Σ}.

Lemma wpc_conseq (A:Type) (EA:Enc A) P Q r t (φ:A -> iProp Σ):
  (P =[ true | locs t ]=∗ Q) ->
  (Q -∗ wpc r t φ) -∗
  (P -∗ wpc r t φ).
Proof.
  iIntros (Hsupd) "Hwpc HP".
  iIntros (?) "? ?".
  iApply (wp_conseq with "[-HP] [-]").
  { apply Hsupd. }
  2:iFrame.
  iIntros.
  iApply ("Hwpc" with "[$] [$] [$]").
Qed.

Lemma wpc_free_singleton  (l:loc) r (bs:smultiset.smultiset loc) (b:store.block) t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  l ∉ (locs t) ->
  dom bs ⊆ {[l]} →
  (Stackable l 1%Qp ∗ l ↦ b ∗ l ↤ bs) -∗
  (♢(size_block b) ∗ †l -∗ wpc r t Q) -∗
  wpc r t Q.
Proof.
  iIntros.
  iApply (wpc_conseq with "[$]").
  { eauto using logical_free. }
  iFrame.
Qed.

End Supd.

Section CSupd.
Context `{interpGS Σ}.

Local Notation "P =#=∗ Q" := (P =[true | ∅]=∗ Q)%I
  (at level 99, Q at level 200).

(* Given a supd supposing access to at least the locations of the term,
   we can apply it.
   It allows to give a temporary access to the locations framed by WPC *)
Lemma wpc_esupd_aux (A:Type) (EA:Enc A) P Q k r t (φ:A -> iProp Σ):
  locs t ⊆ (r ∪ dom k) ->
  (P =#=∗ Q) ->
  (Stackables k ∗ Q -∗ wpc r t φ) -∗
  (Stackables k ∗ P -∗ wpc r t φ).
Proof.
  iIntros (? Hs) "Hwp [? ?]".
  iIntros (k' ?) "?".
  iDestruct (Stackables_union with "[$]") as "HS".

  rewrite (@split_map (k' ⋅ k) (locs t)).
  iDestruct "HS" as "(H1 & H2)".
  2:{ rewrite dom_op. set_solver. }
  iApply (@wp_enc_conseq _ _ _ _ (Stackables (restrict (k' ⋅ k) (locs t)) ∗ P)%I (Stackables (restrict (k' ⋅ k) (locs t)) ∗ Q)%I with "[H2 Hwp]").
  { iApply supd_simpl; rewrite dom_restrict dom_op.
    { set_solver. }
    { replace (locs t ∖ ((dom k' ∪ dom k) ∩ locs t)) with (∅:gset loc) by set_solver.
      eauto. } }
  2:iFrame.
  iIntros "(? & ?)".
  iDestruct (Stackables_union with "[$]") as "HS".
  rewrite <- split_map.
  2:{ rewrite dom_op. set_solver. }

  iDestruct "HS" as "(? & ?)".
  iSpecialize ("Hwp" with "[$] [% //] [$]").
  eauto.
Qed.

Lemma wpc_esupd_gen (A:Type) (EA:Enc A) P Q k (r : gset loc) (t : tm) (φ : A → iProp Σ) :
  locs t ⊆ (r ∪ dom k) ->
  (P =#=∗ Q) → Stackables k ∗ P ∗ (Stackables k ∗ Q -∗ wpc r t φ) -∗ wpc r t φ.
Proof.
  iIntros (? ?) "(? & ? & ?)".
  iApply (wpc_esupd_aux with "[$]"); eauto.
  iFrame.
Qed.

Lemma wpc_esupd (A:Type) (EA:Enc A) P Q (r : gset loc) (t : tm) (φ : A → iProp Σ) :
  locs t ⊆ r ->
  (P =#=∗ Q) → P ∗ (Q -∗ wpc r t φ) -∗ wpc r t φ.
Proof.
  iIntros (? ?) "(? & HF)".
  iApply wpc_bupd. iMod Stackables_empty. iModIntro.
  iApply wpc_esupd_gen; last iFrame.
  { set_solver. }
  { eauto. }
  iFrame. iIntros "(? & ?)". iFrame.
  iApply "HF". iFrame.
Qed.

Lemma wpc_confront_Stackable l r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  Stackable l 1%Qp -∗
  (⌜l ∉ r⌝ -∗ Stackable l 1%Qp -∗ wpc r t Q) -∗
  wpc r t Q.
Proof.
  iIntros "? Hwpc".
  iIntros (? ?). iIntros.
  iApply (wp_enc_conseq with "[Hwpc]").
  { apply Stackables_confront_Stackable. }
  { iIntros "(%Hk & ? & ?)".
    iApply ("Hwpc" with "[%] [$] [%] [$]"); try easy.
    set_solver. }
  { iFrame. }
Qed.

Ltac use_conseq lemma :=
  iIntros;
  iApply (wpc_conseq with "[$]");
  first (eauto using lemma);
  iFrame.

Lemma wpc_confront_vmapsfrom v1 v2 q1 q2 ls1 ls2 r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  (is_loc v1 -> is_loc v2 -> 1 < q1 + q2)%Qz ->
  v1 ↤?{q1} ls1 ∗ v2 ↤?{q2} ls2 -∗
  (v1 ↤?{q1} ls1 ∗ v2 ↤?{q2} ls2 ∗ ⌜diff_loc v1 v2⌝  -∗ wpc r t Q) -∗
  wpc r t Q.
Proof. use_conseq vmapsfrom_confront. Qed.

Lemma wpc_cleanup_vsingleton l' v q ls r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  v ↤?{q} ls ∗ †l' -∗
  (v ↤?{q} (ls ⊎ {[-l'-]}) ∗ †l' -∗ wpc r t Q) -∗
  wpc r t Q.
Proof. use_conseq vmapsfrom_cleanup. Qed.

Lemma spec_esupd_free l P n env :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗
    Spec n env P l =#=∗ ♢ (1 + length env) ∗ group_pointedbys ∅ env.*1 env.*2.
Proof.
  iIntros "(? & ? & ?)".
  iIntros (? kwp ?). iIntros.
  iDestruct (spec_free with "[$]") as "Hfree".
  2:{ iMod ("Hfree" $! maxsize kwp σ with "[$]") as "(? & ? & ?)".
      by iFrame. }
  set_solver.
Qed.

End CSupd.

Notation "P =#=∗ Q" := (P =[true | ∅]=∗ Q)%I
  (at level 99, Q at level 200).

Section wpc_more.
Context `{!interpGS Σ}.

Lemma wpc_context_vsingleton (v:val) q r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  vStackable v q ∗ wpc (r ∪ locs v) t (fun w:A => vStackable v q -∗ Q w) -∗
  wpc r t Q.
Proof.
  iIntros "[? ?]".
  destruct v.
  { iApply wpc_context_singleton. iFrame.
    auto_locs. assert ((r ∪ {[z]}) = ({[z]} ∪ r)) as -> by set_solver.
    iFrame. }
  all:auto_locs; rewrite right_id_L; iApply (wpc_mono with "[$]");
    iIntros (?) "H"; by iApply "H".
Qed.

Lemma wpc_cleanup_singleton l' l q ls r t (A:Type) (EA:Enc A)  (Q:A -> iProp Σ) :
   l ↤{q} ls ∗ †l' -∗ (l ↤{q} (ls ⊎ {[-l'-]}) ∗ †l' -∗ wpc r t Q) -∗ wpc r t Q.
Proof.
  iIntros "[? #Hd] Hwp".
  iApply (wpc_conseq with "[Hwp Hd]").
  { apply mapsfrom_cleanup. }
  2:now iFrame.
  iIntros. iApply "Hwp". now iFrame.
Qed.
End wpc_more.

Global Opaque wpc.
