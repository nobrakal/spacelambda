From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From glaneur.fracz Require Import qz smultiset.
From glaneur.spacelang Require Import successors predecessors.
From glaneur.language Require Import language closure notation.
From glaneur Require Import more_space_lang more_maps_and_sets.
From glaneur Require Export utils interp.

From glaneur Require Import wp_closure wp_spec.
From glaneur Require Import interp wp_alloc wp_call wp_load wp_bin_op wp_store.

(******************************************************************************)

Class Enc (A:Type) := enc : A -> val.
Global Instance Enc_unit : Enc unit := fun _ => val_unit.
Global Instance Enc_nat : Enc nat := val_nat.
Global Instance Enc_loc : Enc loc := val_loc.
Global Instance Enc_val : Enc val := id.

Lemma enc_unit (x:unit) :
  enc x = val_unit.
Proof. easy. Qed.
Global Instance inj_enc_unit : @Inj unit val (=) (=) enc.
Proof. intros [] [] ?. easy. Qed.

Lemma enc_nat (x:nat) :
  enc x = val_nat x.
Proof. easy. Qed.
Global Instance inj_enc_nat : @Inj nat val (=) (=) enc.
Proof. intros ? ? E. injection E. easy. Qed.

Lemma enc_loc (x:loc) :
  enc x = val_loc x.
Proof. easy. Qed.
Global Instance inj_enc_loc : @Inj loc val (=) (=) enc.
Proof. intros ? ? E. injection E. easy. Qed.

Lemma enc_val (x:val) :
  enc x = x.
Proof. easy. Qed.
Global Instance inj_enc_val : @Inj val val (=) (=) enc.
Proof. intros ? ? ?. easy. Qed.

Ltac rew_enc_step tt :=
  first [ rewrite enc_unit
        | rewrite enc_nat
        | rewrite enc_loc
        | rewrite enc_val ].

Ltac rew_enc_core tt :=
  repeat (rew_enc_step tt).

Tactic Notation "rew_enc" :=
  rew_enc_core tt.

(******************************************************************************)

Definition post `{Enc A} {Σ : gFunctors} (Q:A -> iProp Σ) : val -> iProp Σ :=
  fun v => (∃ a, ⌜v = enc a⌝ ∗ Q a)%I.

Lemma post_inj `{Enc A} `{Inj A val (=) (=) enc} {Σ : gFunctors} (Q:A -> iProp Σ) :
  forall v, post Q (enc v) ≡ Q v.
Proof.
  intros v.
  iSplit.
  { iIntros "[% [%E ?]]". rewrite inj_iff in E. subst. easy. }
  { iIntros. iExists _.  eauto. }
Qed.

Lemma post_val {Σ : gFunctors} (Q:val -> iProp Σ) :
  forall v, post Q v ≡ Q v.
Proof. intros v. rewrite -(enc_val v) post_inj //. Qed.

Lemma post_unit {Σ : gFunctors} (Q:unit -> iProp Σ) :
  post Q val_unit ≡ Q tt.
Proof. rewrite -(enc_unit tt) post_inj //. Qed.

Lemma post_nat {Σ : gFunctors} (Q:nat -> iProp Σ) :
  forall n, post Q (val_nat n) ≡ Q n.
Proof. intros n. rewrite -(enc_nat n) post_inj //. Qed.

Lemma post_loc {Σ : gFunctors} (Q:loc -> iProp Σ) :
  forall l, post Q (val_loc l) ≡ Q l.
Proof. intros l. rewrite -(enc_loc l) post_inj //. Qed.

#[export] Hint Rewrite @post_val @post_unit @post_nat @post_loc : rew_post.

(******************************************************************************)

Lemma post_strong_mono {Σ : gFunctors} (A:Type) (EA:Enc A) (Q Q':A -> iProp Σ) (v:val) :
  (∀ a, Q a ==∗ Q' a) -∗
  post Q v ==∗ post Q' v.
Proof.
  iIntros "Hq [%a [%E ?]]". subst.
  iExists _. iSplitR; try easy.
  iApply "Hq". easy.
Qed.

Lemma post_mono {Σ : gFunctors} (A:Type) (EA:Enc A) (Q Q':A -> iProp Σ) (v:val) :
  (∀ a, Q a -∗ Q' a) -∗
  post Q v -∗ post Q' v.
Proof.
  iIntros "Hq [%a [%E ?]]". subst.
  iExists _. iSplitR; try easy.
  iApply "Hq". easy.
Qed.

Set Implicit Arguments.

Definition wp_enc `{!interpGS Σ} `{Enc A} (b:bool) (t:tm) (Q:A -> iProp Σ) :=
  wp b t (post Q).

Global Instance wp_enc_ne `{!interpGS Σ} A (EA:Enc A) b t n :
  Proper (pointwise_relation A (dist n) ==> dist n) (wp_enc b t).
Proof.
  revert t. induction (lt_wf n) as [n _ IH]=> t Φ Ψ HΦ.
  unfold wp_enc,post.
  repeat (f_contractive || f_equiv).
Qed.

Lemma wp_enc_eq `{!interpGS Σ} (A:Type) (EA:Enc A) (b:bool) (t:tm) (Q:A -> iProp Σ) :
  wp_enc b t Q = wp b t (post Q).
Proof. easy. Qed.

Lemma wp_wp_enc `{!interpGS Σ} (A:Type) (EA:Enc A) (b:bool) (t:tm) (Q:A -> iProp Σ) :
  wp b t (post Q) -∗ wp_enc b t Q.
Proof. rewrite wp_enc_eq. eauto. Qed.

Lemma wp_enc_strong_mono `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q Q':A -> iProp Σ) :
  wp_enc b t Q -∗ (∀ v, Q v ==∗ Q' v) -∗ wp_enc b t Q'.
Proof.
  iIntros "? ?".
  iApply (wp_strong_mono with "[$]").
  iIntros.
  iApply (post_strong_mono with "[$] [$]").
Qed.

Lemma wp_enc_strong_mono_val `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q:A -> iProp Σ) (Q':val -> iProp Σ) :
  wp_enc b t Q -∗ (∀ v, Q v ==∗ Q' (enc v)) -∗ wp_enc b t Q'.
Proof.
  iIntros "? Hq".
  iApply (wp_strong_mono with "[$]").
  iIntros (?) "[%a [%E ?]]".
  iExists _. iSplitR; try easy.
  by iApply "Hq".
Qed.

Lemma wp_enc_mono `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q Q':A -> iProp Σ) :
  wp_enc b t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wp_enc b t Q'.
Proof.
  iIntros "? HQ".
  iApply (wp_enc_strong_mono with "[$]").
  iIntros.
  by iApply "HQ".
Qed.

Lemma wp_enc_mono_val `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q:A -> iProp Σ) (Q':val -> iProp Σ) :
  wp_enc b t Q -∗ (∀ v, Q v -∗ Q' (enc v)) -∗ wp_enc b t Q'.
Proof.
  iIntros "? HQ".
  iApply (wp_enc_strong_mono_val with "[$]").
  iIntros.
  by iApply "HQ".
Qed.

Lemma wp_enc_if `{!interpGS Σ} (A:Type) (EA:Enc A) b n t1 t2 Q :
  (if (decide (n≠0)) then wp_enc b t1 Q else wp_enc b t2 Q)
    ⊢ wp_enc b (tm_if n t1 t2) Q.
Proof.
  iIntros.
  iApply wp_if.
  now case_decide.
Qed.

Lemma wp_enc_nofree `{!interpGS Σ} (A:Type) (EA:Enc A) b t Q :
  wp_enc false t Q -∗ wp_enc b t Q.
Proof.
  iIntros. iApply wp_nofree. eauto.
Qed.

Lemma wp_enc_bind `{!interpGS Σ} (A:Type) (EA:Enc A) b E L t (Q: A -> iProp Σ) :
  locs E = dom L ->
  wp_enc b t (fun (v:val) => Stackables L -∗ wp_enc b (fill_item E v) Q) -∗
  Stackables L -∗ wp_enc b (fill_item E t) Q.
Proof.
  iIntros (?) "Hwp ?".
  iApply (wp_bind with "[Hwp] [$]"); eauto.
  iApply (wp_mono with "[$]"). iIntros (?) "Hp ?". rewrite post_val.
  iApply "Hp". eauto.
Qed.

Lemma wp_enc_bind_nofree `{!interpGS Σ} (A:Type) (EA:Enc A) b E t Q :
  wp_enc false t (fun (v:val) => wp_enc b (fill_item E v) Q) -∗
  wp_enc b (fill_item E t) Q.
Proof.
  iIntros.
  iApply wp_bind_nofree.
  iApply (wp_mono with "[$]"). iIntros. rewrite post_val.
  iApply (wp_mono with "[$]"). eauto.
Qed.

Lemma wp_enc_let_val `{!interpGS Σ} (A:Type) (EA:Enc A) b x (v:val) t Q :
  wp_enc b (subst' x v t) Q -∗
  wp_enc b (tm_let x v t) Q.
Proof.
  iIntros.
  iApply (wp_let_val with "[$]").
Qed.

Lemma wp_enc_let_nofree `{!interpGS Σ} (A:Type) (EA:Enc A) x t1 t2 b Q :
  wp_enc false t1 (fun v => wp_enc b (subst' x v t2) Q) -∗
  wp_enc b (tm_let x t1 t2) Q.
Proof.
  intros. iIntros "H".
  iApply wp_let_nofree.
  iApply (wp_mono with "[$]").
  iIntros. rewrite post_val. iFrame.
Qed.

Lemma wp_enc_call `{!interpGS Σ} (A:Type) (EA:Enc A) b self args body vs ts (Q:A -> iProp Σ) :
  length args = length vs →
  locs body = ∅ →
  ts = tm_val <$> vs →
  wp_enc b (substs' (zip (self :: args) (val_code self args body :: vs)) body) Q -∗
  wp_enc b (tm_call (val_code self args body) ts) Q.
Proof.
  iIntros.
  iApply wp_call; eauto.
Qed.

Unset Implicit Arguments.

Lemma wp_enc_mk_spec `{!interpGS Σ} P `{LNE P} env lq self args code :
  correct_name self args ->
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  locs code = ∅ ->
  env.*1 = fv_clo' self args code ->
  □(∀ l vs, ⌜length vs = length args⌝ -∗ Spec (length args) (zip env.*2 lq) P l -∗ P l vs (substs env (substs' (zip args vs) (subst' self l code))) (Spec (length args) (zip env.*2 lq) P l)) -∗
  ♢ (1 + length env) ∗ group_pointedbys ∅ env.*2 lq -∗
  wp_enc false (substs env (mk_clo self args code))
  (fun (l:loc) => l ↤ ∅ ∗ Stackable l 1%Qp ∗ Spec (length args) (zip env.*2 lq) P l).
Proof.
  iIntros.
  iApply wp_mk_spec; eauto.
Qed.

Set Implicit Arguments.

Lemma wp_enc_call_spec `{!interpGS Σ} (A:Type) (EA:Enc A) P (vals:list val) b n env l  vs (Ψ: A -> iProp Σ) :
  vs = (tm_val <$> vals) ->
  length vals = n ->
  Spec n env P l -∗
  (∀ t, P l vals t (Spec n env P l) -∗ wp_enc b t Ψ) -∗
  wp_enc b (call_clo l vs) Ψ.
Proof.
  iIntros. subst.
  iApply (wp_call_spec with "[$]"); eauto.
Qed.

Lemma wp_enc_end `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q: A -> iProp Σ) :
  wp_enc b t (fun v:A => wp_enc b (enc v) Q) -∗
  wp_enc b t Q.
Proof.
  iIntros.
  do 2 rewrite wp_enc_eq.
  iApply wp_end.
  iApply (wp_mono with "[$]").
  iIntros (?) "[%a [%Ha ?]]".
  subst. eauto.
Qed.

Lemma wp_enc_end_val `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q: A -> iProp Σ) :
  wp_enc b t (fun v:val => wp_enc b v Q) -∗
  wp_enc b t Q.
Proof.
  iIntros.
  do 2 rewrite wp_enc_eq.
  iApply wp_end.
  iApply (wp_mono with "[$]").
  iIntros (?) "[%a [%Ha ?]]".
  subst. eauto.
Qed.

Lemma wp_enc_free (l:loc) `{!interpGS Σ} (A:Type) (EA:Enc A) (bs:smultiset.smultiset loc) (blk:store.block) t (Q:A -> iProp Σ) :
  l ∉ (locs t) ->
  dom bs ⊆ {[l]} →
  (Stackable l 1%Qp ∗ l ↦ blk ∗ l ↤ bs) -∗
  (♢(size_block blk) ∗ †l -∗ wp_enc true t Q) -∗
  wp_enc true t Q.
Proof.
  iIntros.
  iApply (wp_conseq with "[$]").
  { eauto using logical_free. }
  iFrame.
Qed.

Section Derived.
Context `{interpGS Σ}.

Lemma wp_enc_conseq `{Enc A} P Q b (t : tm) (φ : A → iProp Σ) :
  (P =[ b | locs t ]=∗ Q) → (Q -∗ wp_enc b t φ) -∗ P -∗ wp_enc b t φ.
Proof.
  iIntros (Hlemma) "?".
  iApply (wp_conseq with "[$]").
  eauto.
Qed.

Ltac use_conseq lemma :=
  iIntros;
  iApply (wp_conseq with "[$]");
  first (eauto using lemma);
  iFrame.

Lemma wp_enc_vmapsfrom_confront `{Enc A} v1 v2 q1 q2 ls1 ls2 b t (Q : A → iProp Σ) :
  (is_loc v1 -> is_loc v2 -> 1 < q1 + q2)%Qz ->
  v1 ↤?{q1} ls1 ∗ v2 ↤?{q2} ls2 -∗
  (v1 ↤?{q1} ls1 ∗ v2 ↤?{q2} ls2 ∗ ⌜diff_loc v1 v2⌝  -∗ wp_enc b t Q) -∗
  wp_enc b t Q.
Proof. use_conseq vmapsfrom_confront. Qed.

Lemma wp_enc_cleanup_vsingleton `{Enc A} l' v q ls b t (Q : A → iProp Σ) :
  v ↤?{q} ls ∗ †l' -∗
  (v ↤?{q} (ls ⊎ {[-l'-]}) ∗ †l' -∗ wp_enc b t Q) -∗
  wp_enc b t Q.
Proof. use_conseq vmapsfrom_cleanup. Qed.

End Derived.

Section wp_enc_more.

Lemma wp_enc_cleanup_singleton l' l `{!interpGS Σ} `{Enc A} q ls b t (Q:A -> iProp Σ) :
   l ↤{q} ls ∗ †l' -∗ (l ↤{q} (ls ⊎ {[-l'-]}) ∗ †l' -∗ wp_enc b t Q) -∗ wp_enc b t Q.
Proof.
  iIntros "[? #Hd] Hwp".
  iApply (wp_conseq with "[Hwp Hd]").
  { apply mapsfrom_cleanup. }
  2:now iFrame.
  iIntros. iApply "Hwp". now iFrame.
Qed.

Lemma wp_enc_bupd `{!interpGS Σ} (A:Type) (EA:Enc A) b t (Q:A -> iProp Σ) :
  (|==> wp_enc b t Q) ⊢ wp_enc b t Q.
Proof. iApply wp_bupd. Qed.
End wp_enc_more.

Global Opaque wp_enc.
