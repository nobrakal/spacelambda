From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap binders gmultiset stringmap.

From spacelambda.fracz Require Import qz.
From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.
From spacelambda.language Require Export closure.

From spacelambda Require Import more_maps_and_sets more_space_lang.
From spacelambda Require Import utils interp wp_alloc wp_store wp_load wp_call wp_closure.

(* This file presents [Spec], an abstract predicate for closures. *)

(* Last NonExpansive *)
Global Notation LNE f := (∀ a b c n, Proper (dist n ==> dist n) (f a b c)).

Section Spec.
Context `{interpGS Σ}.

(* LATER make fractional *)

Definition Spec_pre
  (arity : nat) (env: list (val * Qz)) (l:loc)
  (Spec : (loc -d> list val -d> tm -d> iPropO Σ -d> iPropO Σ) -d> iPropO Σ) : (loc -d> list val -d> tm -d> iPropO Σ -d> iPropO Σ) -d> iPropO Σ := λ P,
  (∃ (_:LNE P) P' (_:LNE P') self args code,
    IsClosure env self args code l ∗ ⌜arity = length args⌝ ∗
    let body vs :=
      let fv := fv_clo' self args code in
      (substs (zip fv env.*1)) (substs' (zip args vs) (subst' self l code)) in
    (* The later guards the two occurrences of Spec *)
    ▷ □(∀ vs, ⌜length vs = arity⌝ -∗ (Spec P') -∗ P' l vs (body vs) (Spec P')) ∗
    ▷ □(∀ vs, ⌜length vs = arity⌝ -∗ P' l vs (body vs) (Spec P') -∗ P l vs (body vs) (Spec P))
  )%I.

Local Instance Spec_pre_contractive arity env l : Contractive (Spec_pre arity env l).
Proof.
  rewrite /Spec_pre /=. intros n S S' Hspec P.
  f_equiv.
  repeat (f_contractive || f_equiv); try apply Hspec.
Qed.

(* Spec is defined as a fixpoint over Spec_pre.
   Notice that P is required to be LNE.
   This will be the case if P is (as usually) instantiated with wp/wps *)
Definition Spec arity env P l : iProp Σ :=
  fixpoint (Spec_pre arity env l) P.

Lemma Spec_unfold P arity env l :
  Spec arity env P l ⊣⊢ Spec_pre arity env l (fun P => Spec arity env P l) P.
Proof. apply (fixpoint_unfold (Spec_pre _ _ _)). Qed.

Lemma Spec_weak n e R1 `{LNE R2} l :
  □(∀ vs t, ⌜length vs =n⌝ -∗ (Spec n e R1 l -∗ Spec n e R2 l ) -∗
       R1 l vs t (Spec n e R1 l) -∗ R2 l vs t (Spec n e R2 l)) -∗
  Spec n e R1 l -∗ Spec n e R2 l.
Proof.
  iIntros "#HR".
  iLöb as "IH".
  setoid_rewrite Spec_unfold at 7 8.
  iIntros "[% [%P [% [%e1 [%e2 [%e3 (? & ? & (#HW & #Hpost))]]]]]]".
  iExists _,P,_. iExists e1,e2,e3; iFrame.
  iSplit.
  { do 2 iModIntro. iIntros. iApply "HW"; eauto. }
  { do 2 iModIntro. iIntros. iApply "HR"; eauto.
    iApply ("Hpost" with "[% //]"); eauto. }
Qed.

Lemma wp_mk_spec P `{LNE P} env lq self args code:
  (* If self is not anonymous, then it should not appear in args. *)
  correct_name self args ->
  (* We must give non-zero fraction of pointed-by. *)
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  (* The code must contain no locs. *)
  locs code = ∅ ->
  (* We require the "right" env *)
  env.*1 = fv_clo' self args code ->
  (* The meaning of "Spec" *)
  □(∀ l vs, ⌜length vs = length args⌝ -∗ Spec (length args) (zip env.*2 lq) P l -∗ P l vs (substs env (substs' (zip args vs) (subst' self l code))) (Spec (length args) (zip env.*2 lq) P l)) -∗
  (* Soup is a group on two arguments *)
  ♢ (1 + length env) ∗ group_pointedbys ∅ env.*2 lq -∗
  wp false (substs env (mk_clo self args code))
  (fun v => ∃ l, ⌜v = val_loc l⌝ ∗ l ↤ ∅ ∗ Stackable l 1%Qp ∗ Spec (length args) (zip env.*2 lq) P l).
Proof.
  iIntros (? ? ? Henv) "#Hwp (? & ?)".
  replace (substs env) with (substs (zip env.*1 env.*2)).
  2:{ f_equal. rewrite zip_fst_snd //. }
  rewrite Henv.
  iDestruct (big_sepL2_length with "[$]") as "%Hl".
  iApply (wp_mono with "[-]").
  iApply wp_mk_clo; eauto.
  { rewrite -Henv. do 2 rewrite fmap_length //. }
  { rewrite fmap_length //. iFrame. }
  iIntros (?) "[%l (%Hv & Hclo & ? & ?)]". subst.
  iSpecialize ("Hwp" $! l).
  iExists l. iFrame.
  iSplitR; try easy.
  setoid_rewrite Spec_unfold at 3.
  iExists _,_,_. iExists _,_,_. iFrame.
  rewrite fst_zip; last lia.

  iSplitR; first easy.

  iSplit.
  { do 2 iModIntro. iIntros.
    iApply ("Hwp" with "[%] [$]"). eauto. }
  { do 2 iModIntro. iIntros. eauto. }
Qed.

Lemma wp_call_spec_later P  b n env l vals Ψ :
  (* We must call the closure with the right number of arguments. *)
  length vals = n ->
  (* The spec must entail the post *)
  Spec n env P l -∗
  ▷ (∀ t, P l vals t (Spec n env P l) -∗ wp b t Ψ) -∗
  wp b (call_clo l (tm_val <$> vals)) Ψ.
Proof.
  setoid_rewrite Spec_unfold at 1.
  iIntros (?) "[% [% [% [%self [%args [%code (? & %Hl & (#Hwp & #Hpost))]]]]]] Hp".
  subst.
  iApply (wp_call_clo_later with "[$]"); eauto.
  iModIntro.
  iIntros "(? & ?)".
  iApply "Hp".
  iApply "Hpost"; eauto.
  iApply "Hwp"; eauto.
  setoid_rewrite Spec_unfold at 5.
  do 2 iExists _,_,_. iFrame. iSplitR; try easy.
  eauto.
Qed.

Lemma wp_call_spec P b n env l vals Ψ :
  (* We must call the closure with the right number of arguments. *)
  length vals = n ->
  (* The spec must entail the post *)
  Spec n env P l -∗
  (∀ t, P l vals t (Spec n env P l) -∗ wp b t Ψ) -∗
  wp b (call_clo l (tm_val <$> vals)) Ψ.
Proof.
  iIntros.
  iApply (wp_call_spec_later with "[$]"); eauto.
Qed.

Lemma spec_free P  n env l R :
  l ∉ R ->
  Stackable l 1%Qp ∗ l ↤ ∅ ∗
    Spec n env P l =[ true | R ]=∗ ♢ (1 + length env) ∗ group_pointedbys ∅ env.*1 env.*2.
Proof.
  iIntros (?) "(? & ? & Hspec)".
  rewrite Spec_unfold.
  iDestruct "Hspec" as "[% [% [% [%e0 [%e1 [%e2 (? & %Hn & _)]]]]]]".
  destruct Hn.
  iIntros.
  iMod (closure_free with "[$] [$]") as "(? & ? & ?)"; try easy.
  by iFrame.
Qed.

End Spec.

Section SpecPrime.
Context `{interpGS Σ}.

(* Spec' is a predicate for non-recursive, non-self-destructing closures.
   It is directly derived from Spec. *)

(* [transform_spec] transforms a specification predicate for Spec' into a
   specification predicate for Spec.
   It ignores the location of the closure, and preserves the Spec assertion. *)

Local Definition transform_spec (P:list val -> tm -> iProp Σ) : loc -> list val -> tm -> iProp Σ -> iProp Σ :=
  fun _ vs u spec => (P vs u ∗ spec)%I.

(* [transform_spec P] is LNE for any P. *)
Local Instance transform_spec_lne P : LNE (transform_spec P).
Proof. unfold transform_spec. intros ? ? ? ? ? ? ?. repeat (f_contractive || f_equiv). eauto. Qed.

Definition Spec' arity env P l : iProp Σ := Spec arity env (transform_spec P) l.

Definition binder_in_stringset b (s:stringset) :=
  match b with
  | BAnon => False
  | BNamed x => x ∈ s end.

Lemma wp_mk_spec' P env lq self args code:
  correct_name self args ->
  ¬ (binder_in_stringset self (free_variables code)) ->
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  locs code = ∅ ->
  env.*1 = fv_clo' self args code ->
  □(∀ vs, ⌜length vs = length args⌝ -∗ P vs (substs env (substs' (zip args vs) code))) -∗
  (* Soup is a group on two arguments *)
  ♢ (1 + length env) ∗ group_pointedbys ∅ env.*2 lq -∗
  wp false (substs env (mk_clo self args code))
  (fun v => ∃ l, ⌜v = val_loc l⌝ ∗ l ↤ ∅ ∗ Stackable l 1%Qp ∗ Spec' (length args) (zip env.*2 lq) P l).
Proof.
  iIntros (? ? ? ? ?) "#Hwp ?".
  iApply wp_mk_spec; eauto.
  iModIntro. iIntros.
  iSpecialize ("Hwp" with "[%//]").
  replace (subst' self l code) with code.
  2:{ destruct self; try easy. simpl. rewrite subst_not_in //. }
  iFrame "#". iFrame.
Qed.

Lemma wp_call_spec_later' P b n env l vals Ψ :
  length vals = n ->
  Spec' n env P l -∗
  ▷ (∀ t, P vals t -∗ wp b t Ψ) -∗
  wp b (call_clo l (tm_val <$> vals)) (fun v => Ψ v ∗ Spec' n env P l).
Proof.
  iIntros (?) "? HP".
  iApply (wp_call_spec_later with "[$]"); eauto.
  iModIntro.
  iIntros (?) "(?&?)".
  iSpecialize ("HP" with "[$]").
  iApply (wp_mono with "[$]").
  iIntros. by iFrame.
Qed.

Lemma spec_free' P n env l R :
  l ∉ R ->
  Stackable l 1%Qp ∗ l ↤ ∅ ∗
    Spec' n env P l =[ true | R ]=∗ ♢ (1 + length env) ∗ group_pointedbys ∅ env.*1 env.*2.
Proof. apply spec_free. Qed.

End SpecPrime.

Global Opaque Spec.
Global Opaque Spec'.
