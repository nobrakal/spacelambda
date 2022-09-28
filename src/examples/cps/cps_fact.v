From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From glaneur.fracz Require Import qz qz_cmra smultiset_cmra.
From glaneur.language Require Import notation closure.

From glaneur Require Import utils interp more_space_lang wp_all wpc triple.
From glaneur Require Import wp_closure wp_spec.

From glaneur.examples Require Import diaframe tactics.

(*
let rec fac_aux n k =
  if n <> 0
  then
    let k' = fun x -> k (n*x) in
    fac_aux (n-1) k'
  else
    k 1

let fac n = fac_aux n (fun x -> x)
 *)


(******************************************************************************)
(* First about the identity closure *)

Definition id_clo : tm :=
  mk_clo BAnon [["x"]]%binder ("x").

Section Id.
Context `{interpGS Σ}.

Definition id_spec (A:Type) {EA:Enc A} (_:loc) (args:list val) (t:tm) spec : iProp Σ :=
  ∀ (n:A),
  ⌜args = [enc n:val]⌝ -∗
  wps (Some ∅) t (fun m => ⌜m=n⌝ ∗ spec)%I.

Global Instance ne_id_nat (A:Type) {EA:Enc A} : LNE (id_spec A).
Proof. lne. Qed.

Lemma clo_id_spec (A:Type) (EA:Enc A) :
  CODE id_clo
  PRE (♢ 1)
  POST (fun l => Stackable l 1%Qp ∗ l ↤ ∅ ∗ Spec 1 nil (id_spec A) l).
Proof.
  iIntros.
  wps_nofree.
  wps_apply (wps_mk_spec _ nil nil).
  1-3:compute_done.
  { vm_compute. now constructor. }
  { iModIntro. iIntros. iIntros (?) "%Hn".
    simplify_substs. do 2 (destruct vs as [|? vs]; try easy). simpl.
    injection Hn. intros. subst.
    iStepsS. }
  rew_qz. iFrame. iSplitR.
  { unfold group_pointedbys. simpl. easy. }
  iStepsS.
Qed.

Definition id_spec_autodestroy (A:Type) {EA:Enc A} (l:loc) (args:list val) (t:tm) (_:iProp Σ) : iProp Σ :=
  ∀ (n:A) qp,
  ⌜args = [enc n:val]⌝ -∗
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ vStackable (enc n) qp -∗
  wps (Some ∅) t (fun m => ⌜m=n⌝∗ vStackable (enc n) qp ∗ ♢1)%I.

Global Instance ne_id_nat_autodestroy (A:Type) {EA:Enc A} : LNE (id_spec A).
Proof. lne. Qed.

Lemma clo_id_spec_autodestroy (A:Type) (EA:Enc A) :
  CODE id_clo
  PRE (♢ 1)
  POST (fun l => Stackable l 1%Qp ∗ l ↤ ∅ ∗ Spec 1 nil (id_spec_autodestroy A) l).
Proof.
  iIntros.
  wps_nofree.
  wps_apply (wps_mk_spec (id_spec_autodestroy A) nil nil).
  1-3:compute_done.
  { vm_compute. now constructor. }
  { iModIntro. iIntros. iIntros (? ?) "%Hn".
    simplify_substs. do 2 (destruct vs as [|? vs]; try easy). simpl.
    iIntros "(? & ? & ?)".
    injection Hn. intros. subst.
    iDestruct (vStackable_confront (enc n) l qp with "[$]") as "%Hd".

    wps_context (enc n).
    iApply wps_esupd.
    { set_solver. }
    { apply spec_esupd_free. }
    iFrame.
    iIntros "(? & ?)".  wps_val.
    iIntros. iFrame.
    iSplitR; try easy. conclude_diamonds. }
  rew_qz. iFrame. iSplitR.
  { unfold group_pointedbys. simpl. easy. }
  iStepsS.
Qed.
End Id.

(******************************************************************************)
(* The actual code of fac *)

Definition fac_aux : val :=
  μ: "self", [["n", "cont"]],
    if: "n"
    then
      let: "ncont" :=
        mk_clo BAnon [["r"]]%binder
          (let: "p" := "n" '* "r" in call_clo "cont" [["p"]]) in
      let: "m" := "n" '- 1 in
      "self" [["m", "ncont"]]
    else call_clo "cont" [[1]].

Definition fac : val :=
  λ: [["n"]],
    let: "id" := id_clo in
    fac_aux [["n", "id"]].

Section Fac.
Context `{interpGS Σ}.

(* clo_cont_spec specifies [t] to return a natural [r] stratifying [Q r n]
   The whole body must have access to [inv], a invariant of [t].
   Moreover, [t] preserves its spec. *)
Definition clo_cont_spec (Q : nat -> nat -> Prop) inv (_:loc) (args:list val) (t:tm) spec : iProp Σ :=
  ∀ (n:nat),
  ⌜args = [n:val]⌝ -∗
  inv -∗
  wps (Some ∅) t (fun (r:nat) => ⌜Q r n⌝ ∗ inv ∗ spec)%I.

Local Instance lne_clo_cont_spec Q inv : LNE (clo_cont_spec Q inv).
Proof. lne. Qed.

(* Spec_clo_cont specifies the continuation l _and_ bundles what is needed to fire it. *)
Definition Spec_clo_cont (Q:nat -> nat -> Prop) (inv:iProp Σ) (env:list (val * Qz)) (l:loc) : iProp Σ :=
  inv ∗ Spec 1 env (clo_cont_spec Q inv) l.

(* The specification of [spec_aux] *)
Lemma fac_aux_spec Q (n:nat) (cont:loc) inv env :
  CODE (fac_aux [[n,cont]])
  PRE (♢ (3*n) ∗ cont ↤ ∅ ∗ Spec_clo_cont Q inv env cont)
  POST (fun (r:nat) => ⌜Q r (fact n)⌝ ∗ ♢ (3*n) ∗ cont ↤ ∅ ∗ Spec_clo_cont Q inv env cont).
Proof.
  iStartProof.
  iRevert (cont inv env Q).
  iInduction (n) as [] "IH"; iIntros (cont inv env Q) "(Hdiams & Hcont)"; wps_call; wps_if.
  { simplify_substs.
    iDestruct "Hcont" as "(? & ? & ?)".
    wps_call. iFrame. iIntros (?) "Hspec".
    iSpecialize ("Hspec" with "[% //] [$]").
    iApply (@wps_mono with "[$]").
    iIntros (?) "(? & ? & ?)". iFrame. }

  rewrite (subst_not_in "self"). 2:now vm_compute.

  (* LATER *)
  wps_bind_empty idtac; try easy.

  mine 3.
  wps_nofree.
  wps_apply (wps_mk_spec (clo_cont_spec (fun r m => Q r (S n * m)) (Spec_clo_cont Q inv env cont)) [("n", (S n):val) ; ("cont", cont:val)] [1%Qz; 1%Qz] ).
  1-4:compute_done.
  { iModIntro. simpl. iIntros (? ?) "%Hv Hspec".
    do 2 (destruct vs as [|? vs]; try easy).

    (* LATER *)
    simplify_substs.
    rewrite subst_call_clo //. simpl.
    clear Hv. unfold clo_cont_spec.
    iIntros (?) "%Hv (? & ?)". inversion Hv. subst. clear Hv.

    iApply wps_let_nofree.
    iStepsS. simplify_substs.

    wps_call. iFrame.
    iIntros (?) "Hspec_cont".
    iSpecialize ("Hspec_cont" with "[% //] [$]").
    iApply (wps_mono with "[$]").
    iIntros (?) "(? & ?)". iFrame. }
  iDestruct "Hcont" as "(? & ? & ?)".
  simpl. rew_qz. iFrame. simpl.
  iSplitR; first easy.
  iIntros (ncont) "(? & ? & Hspec)".

  (* LATER *)
  iApply wps_let_nofree. simpl.
  do 2 iStepS.
  replace (n-0) with n by lia. rewrite enc_loc.
  iApply wps_end. rew_enc. simpl.

  (* Here, we instantiate the induction hypotheses with our new continuation,
     which needs as an invariant the specification of the old one.  *)
  iSpecialize ("IH" $! ncont (Spec_clo_cont Q inv env cont)).
  wps_apply "IH" as "(%Hv & ?)"; subst.
  iSplitL "Hdiams". conclude_diamonds.
  iIntros (?) "(% & H1 & H2 & (? & H3))".

  iApply wps_esupd.
  { set_solver. }
  { apply (spec_esupd_free ncont). }
  iFrame.
  iIntros "(? & (_ & ? & _) )". simpl.
  wps_val. iFrame. iFrame "%". conclude_diamonds.
Qed.

Lemma fac_spec (n:nat) :
  CODE (fac [[n]])
  PRE (♢ (3*n+1))
  POST (fun (m:nat) => ⌜m=fact n⌝ ∗ ♢(3*n+1)).
Proof.
  iIntros "Hdiams".

  wps_call.

  simplify_substs.
  wps_bind.
  mine 1.
  wps_apply (clo_id_spec nat _) as (l) "(Hnl & ? & ?)".

  iApply @wps_end.
  wps_apply (fac_aux_spec (@eq nat) n l True%I nil).
  iSplitR "Hnl".
  { iSplitL "Hdiams". conclude_diamonds.
    iSplitR; try easy.
    iApply Spec_weak; last iFrame.
    iModIntro. iIntros (? ?) "? IH".
    iIntros "H"; iIntros (?) "? _".
    iSpecialize ("H" with "[$]").
    iApply (wps_mono with "[$]").
    iIntros (?) "(? & ?)". iFrame. iSplitR; first easy. iApply "IH". iFrame. }

  iIntros (?) "(%Hv & Hdiams & ? & (_ & ?))". subst.

  iApply wps_esupd.
  { set_solver. }
  { apply spec_esupd_free. }
  iFrame.
  iIntros "(? & _)".
  iDestruct (diamonds_join with "[$]") as "?". simpl.
  rewrite enc_nat.
  wps_val.
  iSplitR; first easy.
  conclude_diamonds.
Qed.

End Fac.
