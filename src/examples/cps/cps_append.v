From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz qz_cmra smultiset_cmra.
From spacelambda.language Require Import notation closure.

From spacelambda Require Import utils interp more_space_lang wp_all wps triple.
From spacelambda Require Import wp_closure wp_spec.

From spacelambda.examples Require Import tactics cps_fact list list_rev.

(* ------------------------------------------------------------------------ *)
(* cps_append with a recursive closure, and its two specifications. *)

Definition cps_append_aux ys self xs k : tm :=
    let: "b" := list_is_nil [[xs]] in
    if: "b"
    then call_clo k [[ys]]
    else
      let: "h" := list_head [[xs]] in
      let: "t" := list_tail [[xs]] in
      let: "nk" :=
        mk_clo BAnon [["r"]]%binder
          (let: "p" := list_cons [["h", "r"]] in call_clo k [["p"]]) in
      call_clo self [["t", "nk"]].

Definition cps_append : val :=
  λ: [["xs","ys"]],
    let: "id" := id_clo in
    let: "aux" := mk_clo "self" [["xs","k"]]%binder (cps_append_aux "ys" "self" "xs" "k") in
    call_clo "aux" [["xs", "id"]].

Section AppendDestruct.
Context `{interpGS Σ}.
Import ListsOf.

Definition clo_cont_spec {A} (R:A -> val -> iProp Σ) xs1 xs2 (Q:loc -> iProp Σ) pre (ocont:loc) (args:list val) (t:tm) (_:iProp Σ) : iProp Σ :=
  ∀ (p3:loc),
  ⌜args = [p3:val]⌝ -∗
  pre ∗ Stackable ocont 1%Qp ∗ ocont ↤ ∅ ∗  Stackable p3 1%Qp ∗ p3 ↤ ∅ ∗ ListOf R (xs1++xs2) p3 -∗
  wps (Some ∅) t Q%I.

Local Instance lne_clo_cont_spec {A} (R:A -> val -> iProp Σ) xs1 xs2 Q pre : LNE (clo_cont_spec R xs1 xs2 Q pre).
Proof. lne. Qed.

Definition Spec_clo_cont {A} (R:A -> val -> iProp Σ) xs1 xs2 Q pre (env:list (val * Qz)) (l:loc) : iProp Σ :=
  pre ∗ Spec 1 env (clo_cont_spec R xs1 xs2 Q pre) l.

Lemma prove_notin_locs_subst l x v t :
  l ∉ locs v ->
  l ∉ locs t ->
  l ∉ locs (subst x v t).
Proof.
  intros.
  intros E.
  apply locs_subst in E. set_solver.
Qed.

(* LATER Inline the def of mk_clo for locs.  Compute _part_ of the def with evars. *)
Lemma locs_tm_mk_clo_eq_inline self args code self' fv code' :
  self' = extract_self self args code  ->
  fv = fv_clo self' args code ->
  code' = code_clo self' args code fv ->
  mk_clo self args code =
    (let: self' := tm_alloc (1 + (List.length fv)) in
    (init_clo self' code' fv);;
    self')%T.
Proof. intros. rewrite mk_clo_eq. subst. easy. Qed.

Ltac locs_mk_clo tt :=
  erewrite locs_tm_mk_clo_eq_inline;
  [|now vm_compute | now vm_compute | now vm_compute].

Definition cps_append_aux_spec_destructive {A} (R:A -> val -> iProp Σ) L2 l2 (self:loc) (args:list val) t (spec:iProp Σ) : iProp Σ :=
  ∀ L1 (l1:loc) Q (cont:loc) pre env,
  ⌜args = [l1:val;cont:val]⌝ -∗
 (♢(3*(length L1))%nat ∗ Stackable self 1%Qp ∗ self ↤ ∅ ∗ ListOf R L1 l1 ∗ Stackable l1 1%Qp ∗ l1 ↤ ∅ ∗ ListOf R L2 l2 ∗ Stackable l2 1%Qp ∗ Stackable cont 1%Qp ∗ cont ↤ ∅ ∗ Spec_clo_cont R L1 L2 Q pre env cont) -∗
  wps (Some ∅) t (fun v => Q v ∗ ♢ (3*(length L1) + 3))%I.

Definition Spec_cps_append_aux {A} (R:A -> val -> iProp Σ) L2 (l2:loc) l : iProp Σ :=
  Spec 2 [(l2:val,1%Qz)] (cps_append_aux_spec_destructive R L2 l2) l.

Local Instance lne_cps_append_aux_spec {A} (R:A -> val -> iProp Σ) L2 l2 : LNE (cps_append_aux_spec_destructive R L2 l2).
Proof. lne. Qed.

Lemma prove_cps_append_aux_spec {A} self (R:A -> val -> iProp Σ) L1 l1 L2 l2 Q (cont:loc) pre env :
  CODE (subst "k" cont (cps_append_aux l2 self l1 "k"))
  PRE ( ♢(3*(length L1))%nat ∗ Spec 2 [((#l2)%V, 1%Qz)] (cps_append_aux_spec_destructive R L2 l2) self ∗ Stackable self 1%Qp ∗ self ↤ ∅ ∗ ListOf R L1 l1 ∗ Stackable l1 1%Qp ∗ l1 ↤ ∅ ∗ ListOf R L2 l2 ∗ Stackable l2 1%Qp ∗
          Stackable cont 1%Qp ∗ cont ↤ ∅ ∗ Spec_clo_cont R L1 L2 Q pre env cont)
  POST (fun v => Q v ∗ ♢ (3*(length L1) + 3) ).
Proof.
  iStartProof.
  unfold cps_append_aux. simplify_substs.
  rewrite subst_call_clo //. simpl.
  iIntros "(Hdiams & Hspec & H1 & H2 & ? & ? & ? & ? & ? & ? & ? & Hclo)".
  destruct L1 as [|(x,(q,p)) L1].
  { (* LATER grep for this. Ugly. *)
    do 3 iDestruct (Stackables_union with "[$]") as "?".
    iApply (@wps_let_tac loc _ _ _ {[l1;l2;cont;self]} with "[$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply list_is_nil_spec as (v) "(%Hv & ?)". simpl.
    iIntros "(((? & ?) & ?) & H1)".
    wps_if. rewrite decide_True.
    2:{ now apply Hv. }

    simplify_substs.
    iDestruct (Stackable_confront l1 l2 with "[$]") as "%".
    iDestruct (Stackable_confront l1 cont with "[$]") as "%".

    (* LATER *)
    rewrite (ListOf_eq _ _ l1).
    wps_free l1.

    iDestruct (Stackable_confront self l2 with "[$]") as "%".
    iDestruct (Stackable_confront self cont with "[$]") as "%".

    iApply (wps_conseq with "[-Hspec H1 H2]").
    { eapply (spec_free _ _ _ self). set_solver. }
    2:{ iFrame.  }
    iIntros "(? & (? & _))". simpl.

    iDestruct "Hclo" as "(? & ?)". simplify_substs.
    iApply (wps_call_spec with "[$]").
    { rewrite <- (fmap_to_val_force [(#l2)%V:tm]); eauto. }
    { eauto. }
    iIntros (?) "Hspec". unfold clo_cont_spec.
    iSpecialize ("Hspec" with "[% //] [$]").
    iApply wps_weak. 2:iApply (wps_mono with "[$]"). easy. iIntros. iFrame. conclude_diamonds. }
  {  do 3 iDestruct (Stackables_union with "[$]") as "?".
    iApply (@wps_let_tac loc _ _ _ {[l1;l2;cont;self]} with "[$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply list_is_nil_spec as (v) "(%Hv & ?)". simplify_substs.
    iIntros.
    wps_if.
    rewrite decide_False.
    2:{ intros E. apply Hv in E. easy. }

    iApply (@wps_let_tac loc _ _ _ {[l1;cont;self]} with "[$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply (list_head_spec _ R l1) as (h) "(? & ? & ? & ?)". simplify_substs.
    iIntros "?".

    iApply (@wps_let_tac_vnotctxs loc _ _ _ ({[cont;self]} ∪ locs h) h with "[$] [$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply (list_tail_spec _ R) as (t) "(? & ? & ? & ?)". simpl.
    rewrite (subst_not_in "t"); last by vm_compute.
    iIntros "(((? & ?) & ?) & ?) ?".

    simplify_substs. wps_bind.

    iDestruct (Stackable_confront with "[$]") as "%".
    iDestruct (Stackable_confront cont l1 with "[$]") as "%".
    iDestruct (vStackable_confront h l1 with "[$]") as "%".
    assert (l1 ∉ locs h) by (destruct h; set_solver).

    iDestruct (vmapsfrom_correct h with "[$]") as "%Hh".

    iApply (@wps_free_singleton _ _ l1 with "[$]").
    { apply prove_notin_locs_subst; eauto.
      apply prove_notin_locs_subst. set_solver.
      auto_locs_goal. set_solver. }
    { set_solver. }

    iIntros "(? & #l1)".
    iApply (wps_cleanup_vsingleton l1 with "[$]"). iIntros "(Hh & _)".
    iApply (wps_cleanup_singleton l1 with "[$]"). iIntros "(? & _)".
    assert (({[+ l1 +]} ⊎ {[-l1-]}) ≡ ∅) as -> by smultiset_solver.

    wps_nofree.
    wps_apply (wps_mk_spec (clo_cont_spec R L1 L2 (fun v => Q v ∗ ♢3)%I (♢ 3 ∗ R x h ∗ vStackable h p ∗ Stackable cont 1%Qp ∗ Spec_clo_cont R ((x, (q, p)) :: L1) L2 Q pre env cont)%I) [("h",h:val);("k",cont:val)] [if is_loc h then q else 1; 1%Qz]).
    1,3,4:compute_done.
    { apply Forall_cons. split; last compute_done.
      destruct (is_loc h); try easy.
      destruct Hh; try eauto.
      smultiset_solver. }
    { iModIntro. iIntros (ocont ? ?) "Hspec".
      do 2 (destruct vs as [|?v ?vs]; try easy). simpl.
      iIntros (l) "%Hv' ((? & ? & ? & ? & (? & ?)) & Ho1 & Ho2 & ? & ? & ?)". injection Hv'. intros ->. clear Hv'.
      simplify_substs.

      iDestruct (Stackable_confront l ocont with "[$]") as "%".
      iDestruct (Stackable_confront cont ocont with "[$]") as "%".

      iDestruct (vStackable_confront h ocont with "[$]") as "%".
      assert (ocont ∉ locs h) by (destruct h; set_solver).

      (* Autodestruct the cont. k *)
      iApply (wps_conseq with "[-Hspec Ho1 Ho2]").
      { eapply (spec_free _ _ _ ocont). set_solver. }
      2:{ iFrame. }
      iIntros "(? & (Hh & ? & _))". simpl.

      iAssert (h ↤?{q} ∅)%I with "[Hh]" as "?".
      { destruct h; eauto. }

      wps_bind.
      wps_apply list_cons_spec as (?) "(? & ? & ?)".
      { intros. destruct (is_loc h); eauto. destruct Hh; eauto. smultiset_solver. }
      iIntros. simplify_substs.
      wps_call_spec as "Hspec".
      iSpecialize ("Hspec" with "[%//] [$]").
      iApply (wps_mono with "[$]"). iIntros.
      iFrame. conclude_diamonds. }
    simpl.
    rew_qz. iFrame.
    iSplitL "Hh".
    { destruct h; eauto. }
    iIntros (?) "(? & ? & ?) (? & ?)". rewrite enc_loc.

    simplify_substs. wps_call. iFrame. iIntros (?) "Hspec".

    iSpecialize ("Hspec" $! L1 t (λ v1 : loc, Q v1 ∗ ♢ 3)%I with "[% //] [-]").
    { iFrame. mine 3. iFrame. conclude_diamonds. }
    unfold Spec_clo_cont.

    iApply (wps_mono with "[$]").
    iIntros (?) "((? & ?) & ?)".
    iFrame.
    conclude_diamonds. }
Qed.

Lemma cps_append_spec_destructive {A} (R:A -> val -> iProp Σ) L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  PRE ( ♢ (3*(length L1) + 3) ∗ ListOf R L1 l1 ∗ Stackable l1 1%Qp ∗ l1 ↤ ∅ ∗ ListOf R L2 l2 ∗ Stackable l2 1%Qp ∗ l2 ↤ ∅)
  POST (fun l => ListOf R (L1++L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢ (3*(length L1) + 4)).
Proof.
  iIntros "(HD & ? & ? & ? & ? & ? & ?)".
  wps_call. simplify_substs.

  iDestruct (Stackables_union with "[$]") as "?".
  iApply (@wps_let_tac loc _ _ _ {[l1;l2]} with "[$]").
  { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
  { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

  mine 1.
  wps_apply (clo_id_spec_autodestroy loc _) as (id) "(? & ? & Hid) (? & ?)".

  simplify_substs.
  wps_bind.

  wps_nofree.
  wps_apply (wps_mk_spec (cps_append_aux_spec_destructive R L2 l2) [("ys",l2:val)] [1%Qz]).
  1-4:compute_done.
  { iModIntro.
    iIntros (? ? _) "?". clear L1 l1. iIntros (L1 l1 ? ? ? ? Hargs).
    destruct vs as [|v vs]; try easy.
    destruct vs as [|v' vs]; try easy.
    destruct vs; try easy.
    injection Hargs. intros. subst v v'. clear Hargs. simpl.
    simplify_substs.
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iDestruct (@prove_cps_append_aux_spec _ l R L1 l1 L2 l2 Q cont pre env with "[$]") as "?".
    unfold cps_append_aux. simpl. simplify_substs.
    iFrame. }

  mine 2. iFrame.

  iIntros (?) "(? & ? & ?) (? & ?)". simplify_substs. rewrite enc_loc.

  wps_call. iFrame. iIntros (?) "Hspec".
  replace ((length L1 + (length L1 + (length L1 + 0)) + 3 - 1 - 2)) with (3*length L1) by lia.
  unfold cps_append_aux_spec_destructive.

  iAssert (Spec_clo_cont R L1 L2 (λ l : loc, ListOf R (L1 ++ L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢ 1)%I True [] id) with "[Hid]" as "?".
  { iSplitR; eauto.
    iApply (Spec_weak with "[] [$]"); last first.
    iModIntro. iIntros (? ? ?) "HK Hid". iIntros (?) "%".
    iIntros "(_ & ? & ? & ? & ? & ?)".
    iSpecialize ("Hid" with "[% //] [$]").
    iApply (wps_mono with "[$]").
    iStepsS. }

  iSpecialize ("Hspec" $! L1 l1 (fun l => ListOf R (L1++L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢1)%I id True%I nil with "[% //] [$]"). iFrame.
  iApply (wps_mono with "[$]"). simpl.

  iIntros (?) "((? & ? & ? & ?) & ? & ?)".
  iFrame.
  conclude_diamonds.
Qed.

(* A version with List. *)
Import Lists.

Lemma cps_append_spec_destructive_ L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  PRE ( ♢ (3*(length L1) + 3) ∗ List L1 l1 ∗ Stackable l1 1%Qp ∗ l1 ↤ ∅ ∗ List L2 l2 ∗ Stackable l2 1%Qp ∗ l2 ↤ ∅)
  POST (fun l => List (L1++L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢ (3*(length L1) + 4)).
Proof. apply cps_append_spec_destructive. Qed.
End AppendDestruct.

Section Append.
Context `{interpGS Σ}.
Import Lists.

Ltac locs_mk_clo tt :=
  erewrite locs_tm_mk_clo_eq_inline;
  [|now vm_compute | now vm_compute | now vm_compute].

Definition cps_append_aux_spec' L2 l2 (self:loc) (args:list val) t (spec:iProp Σ) : iProp Σ :=
  ∀ L1 (l1:loc) Q (cont:loc) pre env,
  ⌜args = [l1:val;cont:val]⌝ -∗
 (♢(3*(length L1) + 3*(length L1))%nat ∗ Stackable self 1%Qp ∗ self ↤ ∅ ∗ List L1 l1 ∗ List L2 l2 ∗ Stackable l2 1%Qp ∗ Stackable cont 1%Qp ∗ cont ↤ ∅ ∗ Spec_clo_cont (fun x y => ⌜x=y⌝)%I (halves L1) L2 Q pre env cont) -∗
  wps (Some {[l1]}) t (fun v => Q v ∗ List (halves L1) l1 ∗ ♢ (3*(length L1) + 2))%I.

Definition Spec_cps_append_aux' L2 (l2:loc) l : iProp Σ :=
  Spec 2 [(l2:val,1%Qz)] (cps_append_aux_spec' L2 l2) l.

Local Instance lne_cps_append_aux_spec'  L2 l2 : LNE (cps_append_aux_spec' L2 l2).
Proof. lne. Qed.

Lemma prove_cps_append_aux_spec' self L1 l1 L2 l2 Q (cont:loc) pre env :
  CODE (subst "k" cont (cps_append_aux l2 self l1 "k"))
  SOUV {[l1]}
  PRE ( ♢ (3*(length L1) + 3*(length L1))%nat ∗ Spec 2 [((#l2)%V, 1%Qz)] (cps_append_aux_spec' L2 l2) self ∗ Stackable self 1%Qp ∗ self ↤ ∅ ∗ List L1 l1 ∗ List L2 l2 ∗ Stackable l2 1%Qp ∗
          Stackable cont 1%Qp ∗ cont ↤ ∅ ∗ Spec_clo_cont (fun x y => ⌜x=y⌝)%I (halves L1) L2 Q pre env cont)
  POST (fun v => Q v ∗ List (halves L1) l1 ∗ ♢ (3*(length L1) + 2)).
Proof.
  iIntros "(Hdiams & Hspec & H1 & H2 & ? & ? & ? & ? & ? & ? & Hclo)".
  destruct L1 as [|(x,(q,p)) L1].
  {  (* LATER grep for this. Ugly. *)
    do 2 iDestruct (Stackables_union with "[$]") as "?".
    iApply (@wps_let_tac loc _ _ _ {[l1;l2;cont;self]} with "[$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply list_is_nil_spec as (v) "(%Hv & ?)". simpl.
    iIntros "((? & ?) & H1)".
    wps_if. rewrite decide_True.
    2:{ now apply Hv. }

    simplify_substs.

    iDestruct (Stackable_confront self l2 with "[$]") as "%".
    iDestruct (Stackable_confront self cont with "[$]") as "%".

    iApply (wps_conseq with "[-Hspec H1 H2]").
    { eapply (spec_free _ _ _ self). set_solver. }
    2:{ iFrame.  }
    iIntros "(? & (? & _))". simpl.

    iApply (wps_call_spec with "[$]").
    { rewrite <- (fmap_to_val_force [(#l2)%V:tm]); eauto. }
    { eauto. }
    iIntros (?) "Hspec".
    iSpecialize ("Hspec" with "[% //] [$]").

    iApply (@wps_weak _ _ loc _ ∅). set_solver.
    iApply (wps_mono with "[$]"). iIntros. iFrame. conclude_diamonds. }
  { do 2 iDestruct (Stackables_union with "[$]") as "?".
    iApply (@wps_let_tac loc _ _ _ {[l1;l2;cont;self]} with "[$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply list_is_nil_spec as (v) "(%Hv & ?)". simplify_substs.
    iIntros.
    wps_if.
    rewrite decide_False.
    2:{ intros E. apply Hv in E. easy. }

    iApply (@wps_let_tac loc _ _ _ {[l1;cont;self]} with "[$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply (list_head_spec l1) as (h) "(% & Hmf & (Hh1 & Hh2) & ?)". subst x. simplify_substs.
    iIntros "?".

    iApply (@wps_let_tac_vnotctxs loc _ _ _ ({[cont;self]} ∪ locs h) h with "[$] [$]").
    { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
    { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }

    wps_apply list_tail_spec as (t) "(? & ? & Ht1 & Ht2)". simpl.
    rewrite (subst_not_in "t"); last by vm_compute.
    iIntros "((? & ?) & ?) ?".

    simplify_substs.
    wps_bind.

    iDestruct (vmapsfrom_correct h with "[$]") as "%Hh".
    assert (is_loc h -> (q/2)%Qz ≠ 0).
    { intros. destruct Hh; eauto.
      intros E. apply Qz_div_eq_zero in E.
      assert (AllNeg {[+ l1 +]}); smultiset_solver. }

    iAssert (h ↤?{q/2} {[+l1+]} ∗ h ↤?{q/2} ∅)%I with "[Hmf]" as "(Hh' & Hh)".
    { iApply vmapsfrom_split.
      1,2:smultiset_solver.
      rewrite Qz_div_2 right_id. iFrame. }

    wps_nofree.
    wps_apply (wps_mk_spec (clo_cont_spec (fun x y => ⌜x=y⌝)%I (halves L1) L2 (fun v => Q v ∗ ♢3)%I (♢ 3 ∗ vStackable h (p/2)%Qp ∗ Stackable cont 1%Qp ∗ Spec_clo_cont (fun x y => ⌜x=y⌝)%I ((h, ((q/2)%Qz, (p/2)%Qp)) :: halves L1) L2 Q pre env cont)%I) [("h",h:val);("k",cont:val)] [if is_loc h then (q/2)%Qz else 1; 1%Qz]).
    1,3,4:compute_done.
    { apply Forall_cons. split; last compute_done.
      destruct (is_loc h); eauto. }
    { iModIntro. iIntros (ocont ? ?) "Hspec".
      do 2 (destruct vs as [|?v ?vs]; try easy). simpl.
      iIntros (l) "%Hv' ((? & ? & ? & (? & ?)) & Ho1 & Ho2 & ? & ? & ?)". injection Hv'. intros ->. clear Hv'.
      simplify_substs.

      iDestruct (Stackable_confront l ocont with "[$]") as "%".
      iDestruct (Stackable_confront cont ocont with "[$]") as "%".

      iDestruct (vStackable_confront h ocont with "[$]") as "%".
      assert (ocont ∉ locs h) by (destruct h; set_solver).

      (* Autodestruct the cont. k *)
      iApply (wps_conseq with "[-Hspec Ho1 Ho2]").
      { eapply (spec_free _ _ _ ocont). set_solver. }
      2:{ iFrame. }
      iIntros "(? & (Hh & ? & _))". simpl.

      iAssert (h ↤?{q/2} ∅)%I with "[Hh]" as "?".
      { destruct h; eauto. }

      wps_bind.
      wps_apply list_cons_spec as (?) "(? & ? & ?)".
      { intros. destruct (is_loc h); eauto. }
      iIntros. simplify_substs.
      wps_call_spec as "Hspec".
      unfold List.
      iSpecialize ("Hspec" with "[%//] [$]").
      iApply (wps_mono with "[$]"). iIntros.
      iFrame. conclude_diamonds. }
    simpl.
    rew_qz. iFrame. mine 3 as "Hd".
    iSplitL "Hh Hd".
    { destruct h; eauto. iFrame. }
    iIntros (?) "(? & ? & ?) (? & ?)". rewrite enc_loc.

    simplify_substs.

    iApply (wps_context_singleton t). iFrame.
    iApply (@wps_weak _ _ loc _ {[t]}). set_solver.

    wps_call_spec as "Hspec".
    iSpecialize ("Hspec" with "[%//] [-Hh1 Ht1 Ht2 Hh']").
    { iFrame. mine 3. iFrame. conclude_diamonds. }

    iApply (wps_mono with "[$]").

    iIntros (?) "((? & H3) & ? & Hd) ?".
    iFrame. iSplitR "H3 Hd".  2:conclude_diamonds.
    iExists _,_. iFrame.
    eauto. }
Qed.

Lemma cps_append_spec_preserving L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  SOUV {[l1]}
  PRE ( ♢ (3*(length L1) + 3*(length L1) + 3)%nat ∗ List L1 l1 ∗ List L2 l2 ∗ Stackable l2 1%Qp ∗ l2 ↤ ∅)
  POST (fun l => List (halves L1++L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢ (3*(length L1) + 3)).
Proof.
  iIntros "(HD & ? & ? & ? & ?)".
  wps_call.

  iApply (@wps_let_tac loc _ _ _ {[l1;l2]} with "[$]").
  { auto_locs. locs_mk_clo tt. auto_locs. set_solver. }
  { repeat rewrite dom_op. repeat rewrite dom_singleton. set_solver. }
  repeat (rewrite subst_not_in; last by now vm_compute).

  mine 1.
  wps_apply (clo_id_spec_autodestroy loc _) as (id) "(? & ? & Hid)".
  iIntros.

  simplify_substs.
  wps_bind.

  wps_nofree.
  wps_apply (wps_mk_spec (cps_append_aux_spec' L2 l2) [("ys",l2:val)] [1%Qz]).
  1-4:compute_done.
  { iModIntro.
    iIntros (? ? _) "?". clear L1 l1. iIntros (L1 l1 ? ? ? ? Hargs).
    destruct vs as [|v vs]; try easy.
    destruct vs as [|v' vs]; try easy.
    destruct vs; try easy.
    injection Hargs. intros. subst v v'. clear Hargs. simpl.
    simplify_substs.
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iDestruct (@prove_cps_append_aux_spec' l L1 l1 L2 l2 Q cont pre env with "[$]") as "?".
    unfold cps_append_aux. simpl. simplify_substs.
    iFrame. }

  mine 2. iFrame.

  iIntros (?) "(? & ? & ?) ?". simplify_substs. rewrite enc_loc.

  wps_call. iFrame. iIntros (?) "Hspec".
  unfold cps_append_aux_spec'.

  iAssert (Spec_clo_cont (λ x y : val, ⌜x = y⌝) (halves L1) L2
   (λ l : loc, List (halves L1 ++ L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢ 1) True [] id)%I with "[Hid]" as "?".
  { iSplitR; first easy. iApply (Spec_weak with "[] [$]"); last first.

    iModIntro. iIntros (? ? ?) "HK Hid". iIntros (?) "%".
    iIntros "(_ & ? & ? & ? & ? & ?)".
    iSpecialize ("Hid" with "[% //] [$]").
    iApply (wps_mono with "[$]").
    iStepsS. }

  iSpecialize ("Hspec" $! L1 l1 (fun l => List (halves L1++L2) l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ ♢1)%I id True%I nil with "[% //] [-]"). iFrame. conclude_diamonds.
  iApply (wps_mono with "[$]"). simpl.

  iIntros (?) "((? & ? & ? & ?) & ? & ?)".
  iFrame.
  conclude_diamonds.
Qed.
End Append.

Section PaperAppend.
Context `{interpGS Σ}.
Import Lists.

Lemma cps_append_destructive_spec L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  PRE ( ♢ (3*(length L1) + 3) ∗ List L1 l1 ∗ l1 ↩ ∅ ∗ List L2 l2 ∗ l2 ↩ ∅)
  POST (fun l => List (L1++L2) l ∗ l ↩ ∅ ∗ ♢ (3*(length L1) + 4)).
Proof.
  rewrite hooked_one. simpl. iIntros "(?&?&(?&?)&?&?)".
  wps_apply @cps_append_spec_destructive. rewrite hooked_one.
  iStepsS. rewrite one_qp_qz. iStepsS.
Qed.

Lemma cps_append_preserving_spec L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  SOUV {[l1]}
  PRE ( ♢ (3*(length L1) + 3*(length L1) + 3)%nat ∗ List L1 l1 ∗ List L2 l2 ∗ l2 ↩ ∅)
  POST (fun l => List (halves L1++L2) l ∗ l ↩ ∅ ∗ ♢ (3*(length L1) + 3)).
Proof.
  rewrite hooked_one. simpl. iIntros "(?&?&?&?&?)".
  wps_apply @cps_append_spec_preserving. rewrite hooked_one. iStepsS.
Qed.
End PaperAppend.
