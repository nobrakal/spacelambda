From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.
From spacelambda Require Import more_space_lang more_maps_and_sets.
From spacelambda Require Import interp.

From spacelambda Require Import wp_alloc wp_call wp_load wp_call_prim wp_store wp_closure wp_spec.
From spacelambda Require Export wp_enc wpc.

Section Wps.

Context `{!interpGS Σ}.

Definition wps `{EA:Enc A} (X:option (gset loc)) (t:tm) (Q:A -> iProp Σ) :=
  match X with
  | None => wp_enc false t Q
  | Some R => wpc R t Q end.

Global Instance wps_ne `{!interpGS Σ} A (HA:Enc A) X t n :
  Proper (pointwise_relation A (dist n) ==> dist n) (wps X t).
Proof.
  destruct X; [apply wpc_ne | apply wp_enc_ne].
Qed.

Lemma wps_eq (A:Type) (EA:Enc A) X t (Q :A -> iProp Σ) :
  wps X t Q = match X with
  | None => wp_enc false t Q
  | Some R => wpc R t Q end%I.
Proof. easy. Qed.

(* ------------------------------------------------------------------------ *)
(* Structural rules *)

Lemma wps_strong_mono (A:Type) (EA:Enc A) X t (Q Q':A -> iProp Σ) :
  wps X t Q -∗ (∀ v, Q v ==∗ Q' v) -∗ wps X t Q'.
Proof.
  destruct X; [apply wpc_strong_mono |  apply wp_enc_strong_mono].
Qed.

Lemma wps_mono (A:Type) (EA:Enc A) X t (Q Q':A -> iProp Σ) :
  wps X t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wps X t Q'.
Proof.
  iIntros "? H".
  iApply (wps_strong_mono with "[$]").
  iIntros. by iApply "H".
Qed.

Lemma wps_frame (A:Type) (EA:Enc A) X t P (Q:A -> iProp Σ) :
  P ∗ wps X t Q -∗ wps X t (fun v => P ∗ Q v).
Proof.
  iIntros "[? Hwp]".
  iApply (wps_mono with "Hwp").
  eauto with iFrame.
Qed.

Lemma wps_mono_val (A:Type) (EA:Enc A) X t (Q:A -> iProp Σ) (Q':val -> iProp Σ) :
  wps X t Q -∗ (∀ v, Q v -∗ Q' (enc v)) -∗ wps X t Q'.
Proof.
  destruct X.
  { apply wpc_mono_val. }
  { apply wp_enc_mono_val. }
Qed.

Lemma wps_bupd (A:Type) (EA:Enc A) X t (Q:A -> iProp Σ) :
  (|==> wps X t Q) ⊢ wps X t Q.
Proof.
  destruct X.
  { apply wpc_bupd. }
  { apply wp_enc_bupd. }
Qed.

Lemma wps_end (A:Type) (EA:Enc A) X t (Q:A -> iProp Σ) :
  wps X t (fun a => wps X (enc a) Q) -∗
  wps X t Q.
Proof.
  destruct X.
  { apply wpc_end. }
  { apply wp_enc_end. }
Qed.

Lemma wps_end_val (A:Type) (EA:Enc A) X t (Q:A -> iProp Σ) :
  wps X t (fun v:val => wps X v Q) -∗
  wps X t Q.
Proof.
  destruct X.
  { apply wpc_end_val. }
  { apply wp_enc_end_val. }
Qed.

Lemma wps_weak (A:Type) (EA:Enc A) r1 r2 t (Q:A -> iProp Σ) :
  r1 ⊆ r2 ->
  wps (Some r1) t Q -∗ wps (Some r2) t Q.
Proof.
  apply wpc_weak.
Qed.

Lemma wps_nofree (A:Type) (EA:Enc A) X t (Q:A -> iProp Σ) :
  wps None t Q -∗
  wps X t Q.
Proof.
  destruct X; try easy.
  iIntros.
  iApply wp_wpc.
  iApply wp_enc_nofree.
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Reasoning rules *)

Lemma wps_val (A:Type) (EA:Enc A) X (v:A) (Q:A -> iProp Σ) :
  Q v -∗
  wps X (enc v) Q.
Proof.
  destruct X.
  { apply wpc_val. }
  { simpl. rewrite wp_enc_eq.
    iIntros. iApply @wp_val.
    iExists _. iFrame. eauto. }
Qed.

Lemma wps_if (A:Type) (EA:Enc A) X (n:bool) t1 t2 (Q:A -> iProp Σ) :
  (if n then wps X t1 Q else wps X t2 Q)
  ⊢ wps X (tm_if n t1 t2) Q.
Proof.
  destruct X; [ apply wpc_if | apply wp_enc_if ].
Qed.

Lemma wps_call (A:Type) (EA:Enc A) X self args body vs ts (Q:A -> iProp Σ) :
  length args = length vs →
  locs body = ∅ →
  ts = tm_val <$> vs →
  wps X (substs' (zip (self :: args) (val_code self args body :: vs)) body) Q -∗
  wps X (tm_call (val_code self args body) ts) Q.
Proof.
  destruct X.
  { apply wpc_call. }
  { apply wp_enc_call. }
Qed.

Lemma wps_call_spec (A:Type) (EA:Enc A) P (vals:list val) X n env l  vs (Q: A -> iProp Σ) :
  vs = (tm_val <$> vals) ->
  length vals = n ->
  Spec n env P l -∗
  (∀ t, P l vals t (Spec n env P l) -∗ wps X t Q) -∗
  wps X (call_clo l vs) Q.
Proof.
  destruct X; [apply wpc_call_spec | apply wp_enc_call_spec ].
Qed.

Lemma wps_bind (A:Type) (EA:Enc A) r E t k (Q:A -> iProp Σ) :
  (locs E) ⊆ r ∪ (dom k) ->
  Stackables k -∗
  wps (Some (r ∪ locs E)) t (fun (v:val) => Stackables k -∗ wpc r (fill_item E v) Q) -∗
  wps (Some r) (fill_item E t) Q.
Proof.
  apply wpc_bind.
Qed.

Lemma wps_bind_nofree (A:Type) (EA:Enc A) X E t (Q:A -> iProp Σ) :
  wps None t (fun (v:val) => wps X (fill_item E v) Q) -∗
  wps X (fill_item E t) Q.
Proof.
  destruct X.
  { apply wpc_bind_nofree. }
  { apply wp_enc_bind_nofree. }
Qed.

Lemma wps_let_val (A:Type) (EA:Enc A) X x (v:val) t (Q:A -> iProp Σ) :
  wps X (subst' x v t) Q -∗
  wps X (tm_let x v t) Q.
Proof.
  destruct X.
  { apply wpc_let_val. }
  { apply wp_enc_let_val. }
Qed.

Lemma wps_let (A:Type) (EA:Enc A) r x t1 t2 k (Q:A -> iProp Σ) :
  (locs t2) ⊆ r ∪ (dom k) ->
  Stackables k  -∗
  wps (Some (r ∪ locs t2)) t1 (fun v => Stackables k -∗ wps (Some r) (subst' x v t2) Q) -∗
  wps (Some r) (tm_let x t1 t2) Q.
Proof.
  apply wpc_let.
Qed.

Lemma wps_let_nofree (A:Type) (EA:Enc A) X x t1 t2 (Q:A -> iProp Σ) :
  wps None t1 (fun v => wps X (subst' x v t2) Q) -∗
  wps X (tm_let x t1 t2) Q.
Proof.
  destruct X.
  { apply wpc_let_nofree. }
  { apply wp_enc_let_nofree. }
Qed.

(****)
Lemma wp_wps (A:Type) (EA:Enc A) X t (Q:A -> iProp Σ) :
  wp (match X with | None => false | Some _ => true end) t (post Q) -∗
  wps X t Q.
Proof.
  destruct X.
  { iIntros. iApply wp_wpc. iApply wp_wp_enc. eauto. }
  apply wp_wp_enc.
Qed.

Ltac start_deriv :=
  iIntros; iApply wp_wps;
  iApply (wp_mono with "[-]").

Lemma wps_load (l:loc) (n:nat) q vs X :
  n < length vs ->
  l ↦{q} (BBlock vs) ⊢
  wps X (tm_load l n)
  (fun (v:val) => l ↦{q} (BBlock vs) ∗ ⌜v = vs !!! n⌝).
Proof.
  start_deriv.
  iApply wp_load; eauto.
  iIntros. rewrite post_val. eauto.
Qed.

Lemma wps_call_prim (A:Type) (EA:Enc A) X (p:prim) ts (vs:list val) (w:A) :
  ts = tm_val <$> vs →
  eval_call_prim p vs = Some (enc w) ->
  ⊢ wps X (tm_call p ts) (fun r => ⌜r = w⌝).
Proof.
  intros. subst.
  start_deriv.
  { iApply wp_call_prim. eauto. }
  iIntros. subst. iExists _. eauto.
Qed.

Lemma wps_alloc X (n:nat) :
  ♢ n -∗
  wps X (tm_alloc n)
  (fun (l:loc) =>
     l ↦ (BBlock (replicate n val_unit)) ∗
     l ↤ ∅ ∗
     Stackable l 1%Qp).
Proof.
  start_deriv.
  { iApply wp_alloc. eauto. }
  iIntros (?) "[%l (% & ?)]".
  subst. rewrite post_loc. eauto.
Qed.

Lemma wps_store X (l:loc) (n:nat) v qv lsv vs :
  (is_loc v -> qv <> 0%Qz) ->
  n < length vs ->
  l ↦ (BBlock vs) ∗ v ↤?{qv} lsv ⊢
    wps X (tm_store l n v)
    (fun (_:unit) =>
       l ↦ (BBlock (<[n:=v]> vs)) ∗
         v↤?{qv}(lsv ⊎ {[+ l +]}) ∗
         (vs !!! n)↤?{0}({[-l-]})).
Proof.
  start_deriv.
  iApply wp_store; eauto.
  iIntros (?) "(% & ?)".
  subst. rewrite post_unit.
  eauto.
Qed.

Unset Implicit Arguments.

Lemma wps_mk_spec P `{LNE P} env lq self args code :
  correct_name self args ->
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  locs code = ∅ ->
  env.*1 = fv_clo' self args code ->
  □(∀ l vs, ⌜length vs = length args⌝ -∗ Spec (length args) (zip env.*2 lq) P l -∗ P l vs (substs env (substs' (zip args vs) (subst' self l code))) (Spec (length args) (zip env.*2 lq) P l)) -∗
  ♢ (1 + length env) ∗ group_pointedbys ∅ env.*2 lq -∗
  wps None (substs env (mk_clo self args code))
  (fun (l:loc) => l ↤ ∅ ∗ Stackable l 1%Qp ∗ Spec (length args) (zip env.*2 lq) P l).
Proof.
  apply wp_enc_mk_spec; eauto.
Qed.

Set Implicit Arguments.

Lemma wps_conseq (A:Type) (EA:Enc A) P Q r t (φ:A -> iProp Σ):
  (P =[ true | locs t ]=∗ Q) ->
  (Q -∗ wps (Some r) t φ) -∗
  (P -∗ wps (Some r) t φ).
Proof. apply wpc_conseq. Qed.

Lemma wps_esupd (A:Type) (EA:Enc A) P Q (r : gset loc) (t : tm) (φ : A → iProp Σ) :
  locs t ⊆ r ->
  (P =#=∗ Q) → P ∗ (Q -∗ wps (Some r) t φ) -∗ wps (Some r) t φ.
Proof. apply wpc_esupd. Qed.

Lemma wps_confront_Stackable l r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  Stackable l 1%Qp -∗
  (⌜l ∉ r⌝ -∗ Stackable l 1%Qp -∗ wps (Some r) t Q) -∗
  wps (Some r) t Q.
Proof. apply wpc_confront_Stackable. Qed.

Lemma wps_cleanup_vsingleton l' v q ls X t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  v ↤?{q} ls ∗ †l' -∗
  (v ↤?{q} (ls ⊎ {[-l'-]}) ∗ †l' -∗ wps X t Q) -∗
  wps X t Q.
Proof.
  destruct X.
  { apply wpc_cleanup_vsingleton. }
  { apply wp_enc_cleanup_vsingleton. }
Qed.

Lemma wps_context (A:Type) (EA:Enc A) r' r t Q :
  Stackables r' ∗ wps (Some (dom r' ∪ r)) t (fun v:A => Stackables r' -∗ Q v) -∗
  wps (Some r) t Q.
Proof. apply wpc_context. Qed.

Lemma wps_context_singleton l q r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  Stackable l q ∗ wps (Some ({[l]} ∪ r)) t (fun v:A => Stackable l q -∗ Q v) -∗
  wps (Some r) t Q.
Proof. apply wpc_context_singleton. Qed.

Lemma wps_context_vsingleton (v:val) q r t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  vStackable v q ∗ wps (Some (r ∪ locs v)) t (fun w:A => vStackable v q -∗ Q w) -∗
  wps (Some r) t Q.
Proof. apply wpc_context_vsingleton. Qed.
Lemma wps_cleanup_singleton l' l q ls r t (A:Type) (EA:Enc A)  (Q:A -> iProp Σ) :
  l ↤{q} ls ∗ †l' -∗ (l ↤{q} (ls ⊎ {[-l'-]}) ∗ †l' -∗ wps (Some r) t Q) -∗
  wps (Some r) t Q.
Proof. apply wpc_cleanup_singleton. Qed.

Lemma wps_free_singleton  (l:loc) r (bs:smultiset.smultiset loc) (b:store.block) t (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  l ∉ (locs t) ->
  dom bs ⊆ {[l]} →
  (Stackable l 1%Qp ∗ l ↦ b ∗ l ↤ bs) -∗
  (♢(size_block b) ∗ †l -∗ wps (Some r) t Q) -∗
  wps (Some r) t Q.
Proof. apply wpc_free_singleton. Qed.
End Wps.

Global Opaque wps.
