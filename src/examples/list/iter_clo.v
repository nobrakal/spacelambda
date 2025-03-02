From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz qz_cmra smultiset_cmra.
From spacelambda.language Require Import notation closure.

From spacelambda Require Import utils interp more_space_lang wp_all wps triple.
From spacelambda Require Import wp_closure wp_spec.

From spacelambda.examples.tactics Require Import tactics.
From spacelambda.examples.lib Require Import ref.
From spacelambda.examples.list Require Import list.

(* ------------------------------------------------------------------------ *)
(* We specify and prove a recursive closure inside list_iter. *)

Definition list_iter_aux self xs f : tm :=
  let: "tag" := list_is_nil [[xs]] in
  if: "tag"
  then ()%V
  else
    let: "y" := list_head [[xs]] in
    let: "ys" := list_tail [[xs]] in
    call_clo f [["y"]];;
    call_clo self [["ys"]].

Definition list_iter : val :=
  λ: [["f","l"]] ,
    let: "aux" := mk_clo "self" ["xs":binder] (list_iter_aux "self" "xs" "f" )in
    call_clo "aux" [["l"]].

Section IterClo.
Context `{interpGS Σ}.

Import ListsOf.

Definition list_iter_aux_spec {A}
  f (I:list A -> iProp Σ) (R:A -> val -> iProp Σ) l (args:list val) t spec : iProp Σ:=
  ∀ xs (lst:loc),
  ⌜args = [lst:val]⌝ -∗
  ListOf R xs lst ∗ I xs.*1 -∗
  wps (Some {[lst;f;l]}) t
  (fun _:unit => spec ∗ ListOf R xs lst ∗ I []).

Local Instance lne_list_iter_aux_spec {A} f (I:list A -> iProp Σ) (R:A -> val -> iProp Σ) :
  LNE (list_iter_aux_spec f I R).
Proof. lne. Qed.

Lemma prove_list_iter_aux {A} lst f q l (I:list A -> iProp Σ) (R:A -> val -> iProp Σ) :
  □(∀ x y k, I (x :: k) ∗ R x y -∗ wps (Some ({[f]} ∪ locs y)) (call_clo (#f)%V [[y]])%T (fun _:unit => R x y ∗ I k)) -∗
  Spec 1 [((#f)%V, q)] (list_iter_aux_spec f I R) l -∗
  list_iter_aux_spec f I R l [lst:val] (list_iter_aux l lst f)%T (Spec 1 [((#f)%V, q)] (list_iter_aux_spec f I R) l).
Proof.
  iIntros "#Hf Hclo".
  iIntros (xs llst) "%E (? & HI)". injection E. intros ->. clear E.
  unfold list_iter_aux.
  destruct xs as [|(x,(qp,qz)) xs].
  { wps_bind.
    wps_apply (list_is_nil_spec A R llst nil) as "(%Hv & ?)".
    wps_if. rewrite decide_True.
    2:{ now apply Hv. }
    wps_val. iFrame. }
  { wps_bind.
    wps_apply list_is_nil_spec as "(%Hv & ?)".
    wps_if.
    rewrite decide_False.
    2:{ intros nv. apply Hv in nv. congruence. }
    clear Hv.

    simplify_substs.
    wps_bind.
    wps_apply list_head_spec as (y) "(? & ? & ? & ?)".
    wps_context y.
    wps_bind.

    wps_apply list_tail_spec as (l') "(? & ? & ? & ?)".
    simplify_substs.
    wps_bind.

    iApply (@wps_weak _ _ _ _ ({[f]} ∪ locs y)).
    { set_solver. }

    iDestruct ("Hf" with "[$]") as "Hcall".
    iApply (@wps_mono_val with "[$]").

    iIntros (_) "(? & ?) ?".

    wps_context l'.
    iApply (@wps_weak _ _ unit _ {[l';f;l]}).
    { set_solver. }

    replace ([(#l')%V : tm] : list tm) with (tm_val <$> [l':val] : list tm) by compute_done.
    wps_call_spec as "Hspec".
    iSpecialize ("Hspec" with "[% //] [$]").
    iApply (@wps_mono with "[$]").

    iIntros (_) "(? & ? & ?) ? ?".
    iFrame.
    iExists _,_. iFrame. }
  Unshelve. easy.
Qed.

Lemma iter_spec_remaining {A} (I : list A -> iProp Σ) (R: A -> val -> iProp Σ) xs l f q :
  q ≠ 0%Qz ->
  CODE (list_iter [[#f , l]])
  SOUV ({[l;f]})
  PRE (
  □(∀ x y k, I (x :: k) ∗ R x y -∗
      wpc ({[f]} ∪ locs y) (call_clo (#f)%V [[y]])%T (fun _:unit => R x y ∗ I k)) ∗
    ♢ 2 ∗ ListOf R xs l ∗ I xs.*1 ∗ f ↤{q} ∅)
  POST (fun _:unit => ♢ 2 ∗ ListOf R xs l ∗ I [] ∗ f ↤{q} ∅).
Proof.
  iIntros (?) "(#Hf & Hdiams & ? & ? & Hmf)".
  wps_call.

  wps_bind.
  simplify_substs.

  wps_nofree.
  wps_apply (wps_mk_spec (list_iter_aux_spec f I R) [("f", f:val)] [q]).
  { compute_done. }
  { now constructor. }
  { simpl_locs. set_solver. }
  {  compute_done. }
  { iModIntro. iIntros. simpl.
    do 2 (destruct vs as [|?v vs]; try easy). simpl.
    simplify_substs.
    iApply (prove_list_iter_aux v with "[] [$]").
    iFrame "#". }
  rew_qz. simpl. iFrame.
  iIntros (aux) "(auxmf & ? & ?)".
  rewrite enc_loc.

  simplify_substs.
  iApply wps_end.

  wps_call_spec as "Hspec". simpl.
  wps_context aux.
  replace ({[aux]} ∪ {[l; f]}) with ({[l;f;aux]} : gset loc) by set_solver.
  wps_mono "[-auxmf]".
  { iApply "Hspec"; eauto. iFrame. }
  simpl.

  iIntros (?) "(Hclo & HR & HI) ?".
  rewrite enc_unit.

  iApply @wps_esupd.
  { set_solver. }
  { apply spec_esupd_free. }
  iFrame.
  rew_qz. iIntros "(? & (? & _))". simpl.

  iStepsS. easy.
Qed.

Lemma iter_spec {A} (I : list A -> iProp Σ) (R: A -> val -> iProp Σ) xs l f q :
  q ≠ 0%Qz ->
  CODE (list_iter [[#f , l]])
  SOUV ({[l;f]})
  PRE (
  □(∀ x y k, I k ∗ R x y -∗
      wpc ({[f]} ∪ locs y) (call_clo (#f)%V [[y]])%T (fun _:unit => R x y ∗ I (k ++ [x]))) ∗
    ♢ 2 ∗ ListOf R xs l ∗ I nil ∗ f ↤{q} ∅)
  POST (fun _:unit => ♢ 2 ∗ ListOf R xs l ∗ I xs.*1 ∗ f ↤{q} ∅).
Proof.
  iIntros (Hq) "(#Hf & D & Hl & I & P)".
  pose (J := (λ zs, ∃ ys, I ys ∗ ⌜xs.*1 = ys ++ zs⌝)%I).
  iPoseProof (iter_spec_remaining J R xs l f q Hq with "[$D $Hl $P I]") as "Hit".
  - iSplit. 2: iExists []; iFrame; done.
    iModIntro; iIntros (x y k) "(J & xy)".
    iDestruct "J" as (zs) "(I & %Ex)".
    iSpecialize ("Hf" $! x y zs with "[$]").
    iApply (wpc_mono with "Hf").
    iIntros ([]) "($ & I)".
    iExists (zs ++ [x]); iFrame.
    rewrite Ex -app_assoc //.
  - iApply (wps_mono with "Hit").
    iIntros (v) "($ & $ & J & $)".
    iDestruct "J" as (zs) "(I & ->)".
    rewrite app_nil_r //.
Qed.

End IterClo.
