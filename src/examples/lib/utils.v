From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.language Require Import notation.

From spacelambda Require Import more_space_lang wp_all wpc.
From spacelambda.examples Require Import tactics.

Definition soup `{!interpGS Σ} {A} (R:A -> val -> iProp Σ)
  (r:smultiset loc) (xs:list (A * (Qz * Qp))) (vs:list val) : iProp Σ :=
  ([∗ list] x;v ∈ xs;vs,
     let '(x,(qz,qp)) := x in (R x v ∗ vStackable v qp ∗ v ↤?{qz} r)).

Lemma soup_empty `{!interpGS Σ} A (R:A -> val -> iProp Σ) r :
  ⊢ soup R r nil nil.
Proof. unfold soup. easy. Qed.

Lemma soup_app `{!interpGS Σ} A (R:A -> val -> iProp Σ) e l r ls rs :
  soup R e l ls ∗ soup R e r rs -∗
  soup R e (l++r) (ls ++ rs).
Proof.
  iIntros  "[Hl Hr]".
  iApply (big_sepL2_app with "[Hl] [Hr]"); iFrame.
Qed.

Lemma soup_app_exists `{!interpGS Σ} A (R:A -> val -> iProp Σ) e l r :
  (∃ ls, soup R e l ls) ∗ (∃ rs, soup R e r rs) -∗
  ∃ lrs, soup R e (l++r) (lrs).
Proof.
  iIntros  "[[%ls ?] [%rs ?]]".
  iDestruct (soup_app _ _ _ l with "[$]") as "?".
  iExists _. iFrame.
Qed.

Lemma soup_cleanup `{!interpGS Σ} A (R:A -> val -> iProp Σ) c xs vs L :
  († c ∗ soup R {[+c+]} xs vs)%I =[true | L]=∗
  † c ∗ soup R ∅ xs vs.
Proof.
  iIntros "(? & ?)".
  iInduction xs as [|(?,(?,?))] "IH" forall (vs).
  { iIntros. simpl. now iFrame. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]")
      as "[%v [%vs' (%E & (? & ?& ?) & ?)]]". subst.
    iIntros.
    iMod (vmapsfrom_cleanup with "[$] [$]") as "(? & ? & ?)".
    rewrite disj_union_sinlgeton_opposite.
    fold (soup R {[+c+]} xs vs').
    iMod ("IH" $! vs'  with "[$] [$] [$]") as "(? & ? & ?)".
    now iFrame. }
Qed.

Definition dupf : val * Qp -> val * (Qz * Qp) := fun '(v,q) => (v,(q:Qz,q)).

Lemma soup_mixer `{interpGS Σ} (xs:list (val*Qp)) vs :
  soup (λ x y : val, ⌜x = y⌝) ∅ (dupf <$> xs) vs -∗
  [∗ list] x ∈ xs, (x.1 ↤?{x.2:Qp} ∅ ∗ vStackable (fst x) (snd x)).
Proof.
  iRevert (vs).
  iInduction xs as [|(?,?) xs] "IH"; iIntros (vs).
  eauto.
  destruct vs; eauto.
  simpl. unfold soup. simpl. iIntros "((% & ? & ?) & ?)". subst.
  iFrame. iApply "IH". iFrame.
Qed.
