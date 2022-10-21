From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz qz_cmra smultiset_cmra.
From spacelambda.language Require Import notation closure.

From spacelambda Require Import utils interp more_space_lang wp_all wps triple.
From spacelambda Require Import wp_closure wp_spec.

From spacelambda.examples.tactics Require Import tactics.
From spacelambda.examples.lib Require Import ref.
From spacelambda.examples.counter Require Import counter.
From spacelambda.examples.list Require Import list.

(* ------------------------------------------------------------------------ *)
(* We prove two specifications of List.iter, and use one of them to prove
   an implementation of List.length using a reference.

   We use the other one (that logically liberates its argument) to prove
   an implementation of List.rev *)

Definition list_iter :=
  μ: "self" , [["f","l"]] ,
    let: "tag" := list_is_nil [["l"]] in
    if: "tag"
    then ()%V
    else
      let: "x" := list_head [["l"]] in
      let: "xs" := list_tail [["l"]] in
      call_clo "f" [["x"]];;
      "self" [["f","xs"]].

Definition list_length : val :=
  λ: [["l"]] ,
    let: "r" := ref [[0]] in
    let: "incr" := mk_clo BAnon [BAnon] (incr [["r"]]) in
    list_iter [["incr", "l"]];;
    get [["r"]].

Section Iter.
Context `{interpGS Σ}.

Import ListsOf.

Lemma iter_spec_aux {A} ys (I:list A -> iProp Σ) (R:A -> val -> iProp Σ) xs l f :
  □(∀ x y k, I k ∗ R x y -∗ wps (Some ({[f]} ∪ locs y)) (call_clo (#f)%V [[y]])%T (fun _ => R x y ∗ I (k ++ [x]))) -∗
  ListOf R xs l ∗ I ys -∗
  wps (Some {[l;f]}) (list_iter [[#f , l]])%T (fun _ => ListOf R xs l ∗ I (ys ++ xs.*1)).
Proof.
  iIntros "#Hf".
  iRevert (ys l).
  iInduction xs as [|(x,(qp,qz)) xs] "IH"; iIntros (ys l);
    iIntros "(? & HI)"; wps_call; simplify_substs.
  { wps_bind.
    wps_apply (list_is_nil_spec A R l nil) as "(%Hv & ?)".
    wps_if. rewrite Hv.
    wps_val. iFrame. }
  { wps_bind.
    wps_apply list_is_nil_spec as "(%Hv & ?)".
    wps_if. rewrite Hv.

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
    auto_locs.
    iApply (wps_mono with "[$]").

    iIntros (_) "(? & ?) ?".
    iSpecialize ("IH" with "[$]").
    wps_context l'.
    iApply (@wps_weak _ _ _ _ {[l';f]}).
    { set_solver. }
    iApply (@wps_mono with "[$]").

    iIntros (_) "(? & ?) ? ?".
    rewrite -app_assoc cons_middle. iFrame.
    iExists _,_. iFrame. }
Qed.

(*
Lemma iter_spec_update {A B} (I : list B -> iProp Σ) (R: A -> val -> iProp Σ) (R': B -> val -> iProp Σ) xs l f :
  □(∀ x y k, I k ∗ R x y -∗
      wpc ({[f]} ∪ locs y) (call_clo (#f)%V [[y]])%T (fun _ => ∃ x', R' x' y ∗ I (k ++ [x']))) -∗
  ListOf R xs l ∗ I nil -∗
  wpc {[l;f]} (list_iter [[#f , l]])%T (fun _ => ListOf R' xs l ∗ I (xs.*1)).

specialize with R=R'
 *)

Lemma iter_spec {A} (I : list A -> iProp Σ) (R: A -> val -> iProp Σ) xs l f :
  □(∀ x y k, I k ∗ R x y -∗
      wps (Some ({[f]} ∪ locs y)) (call_clo (#f)%V [[y]])%T (fun _ => R x y ∗ I (k ++ [x]))) -∗
  ListOf R xs l ∗ I nil -∗
  wps (Some {[l;f]}) (list_iter [[#f , l]])%T (fun _ => ListOf R xs l ∗ I (xs.*1)).
Proof.
  iIntros.
  iDestruct (iter_spec_aux nil with "[$] [$]") as "?". simpl.
  iFrame.
Qed.

Lemma length_spec  {A} (R: A -> val -> iProp Σ) xs l :
  ♢ 3 ∗ ListOf R xs l -∗
  wps (Some {[l]}) (list_length [[l]])%T (fun (n:nat) => ⌜n = length xs⌝ ∗ ♢ 3 ∗ ListOf R xs l).
Proof.
  iIntros "(? & ilo)".
  wps_call.

  assert (locs list_iter = ∅) by compute_done.
  assert (locs get = ∅) by compute_done.
  wps_bind.

  mine 2.
  wps_nofree.
  wps_apply ref_spec_no_loc as (r) "(Hr & (? & ?) & ?)".
  { compute_done. }
  iDestruct (Stackables_borrow_Stackable _ r with "[$]") as "(? & ?)".
  { rewrite lookup_singleton //. }

  simplify_substs.
  wps_bind.

  wps_nofree.
  wps_apply (wps_mk_spec (incr_clo_spec r) [("r", val_loc r)] [1%Qz] ).
  1-4:compute_done.
  { iModIntro. iIntros. simpl.
    do 2 (destruct vs; simpl in *; try congruence).
    iApply prove_spec_incr; eauto. }
  simpl. rew_qz. iFrame.
  iIntros (fi) "(Hfimf & ? & Hfi)". iIntros.
  wps_bind.
  wps_context fi.

  wps_mono "[Hfi ilo Hr]".
  { iApply (@wps_weak _ _ _ _ {[l;fi]}).
    { set_solver. }
    iApply (iter_spec (fun xs => isRef ^(length xs) r ∗ Spec 1 [((#r)%V, 1%Qz)] (incr_clo_spec r) fi)%I with "[]").
    2:{ simpl. iFrame. }
    iModIntro. iIntros (? ? ?) "((? & ?) & HR)".

    wps_call_spec as "Hspec".
    iSpecialize ("Hspec" with "[$]").

    wps_mono "[-HR]".
    iApply (@wps_weak with "[$]"). { set_solver. }
    iIntros (_) "(? & ?)". iFrame.
    rewrite app_length. simpl.
    replace (length k + 1) with (S (length k)) by lia. iFrame. }
  iIntros (_) "(? & ? & Hspec)".
  iIntros "Hcfi ?".

  iApply @wps_end.
  wps_nofree.
  wps_apply @get_spec_enc as (m) "[%Hm ?]".
  rewrite fmap_length in Hm.

  iApply @wps_esupd.
  { set_solver. }
  { apply (spec_esupd_free fi). }
  iFrame.
  iIntros "(? & (? & _))".
  simpl.
  iDestruct (Stackable_join with "[$] [$]") as "?".
  rewrite Qp_half_half.
  wps_free r.
  iDestruct (diamonds_join with "[$]") as "?".
  wps_val.
  iSplitR; try easy.
  simpl. rew_qz. iFrame.
Qed.
End Iter.

Definition ref_cons : val :=
  λ: [["x","r"]],
    let: "l" := get [["r"]] in
    let: "l2" := list_cons [["x","l"]] in
    set [["r", "l2"]].

Definition list_rev : val :=
  λ: [["l"]] ,
    let: "acc" := list_nil [] in
    let: "r" := ref [["acc"]] in
    let: "cons" := mk_clo BAnon [BNamed "x"] (ref_cons [["x", "r"]]) in
    list_iter [["cons", "l"]];;
    get [["r"]].

Section HardIter.
Context `{interpGS Σ}.
Import ListsOf.

(* LATER wps_bind should not fail if only r is given, + that f ∈ r *)

Lemma destructive_iter_spec_aux {A} ys (I : list (A * (Qz * Qp)) -> iProp Σ) (R: A -> val -> iProp Σ) xs l f r :
  □(∀ x y k qp qz s, ⌜ys ++ xs = k ++ (x,(qz,qp))::s /\ (is_loc y -> qz ≠ 0%Qz)⌝ -∗ y ↤?{qz} ∅ ∗ vStackable y qp ∗ ♢ 3 ∗ R x y ∗ I k -∗ wps (Some ({[f]} ∪ r)) (call_clo (#f)%V [[y]])%T (fun _ => I (k ++ [(x,(qz,qp))]))) -∗
  ListOf R xs l ∗ I ys ∗ Stackable l 1%Qp ∗ l ↤ ∅ -∗
  wps (Some ({[f]} ∪ r)) (list_iter [[#f , l]])%T (fun _ => ♢ 1 ∗ I (ys ++ xs)).
Proof.
  iRevert (ys l).
  iInduction xs as [|(x,(qp,qz)) xs] "IH"; iIntros (ys l) "#Hf";
    iIntros "(? & HI & ? & ?)"; wps_call; simplify_substs.
  { wps_bind.
    wps_apply (list_is_nil_spec A R l nil) as "(%Hv & ?)". iIntros.
    wps_if. rewrite Hv.
    rewrite ListOf_eq.
    wps_free l.
    wps_val. iFrame. }
  { wps_bind.
    wps_apply list_is_nil_spec as "(%Hv & ?)". iIntros.
    wps_if. rewrite Hv. clear Hv.

    simplify_substs.
    wps_bind.
    wps_apply list_head_spec as (y) "(? & ? & ? & ?)". iIntros.

    simplify_substs. simpl.
    wps_bind.

    wps_apply list_tail_spec as (l') "(? & ? & ? & ?)". iIntros.
    simplify_substs.
    wps_bind.

    iApply (wps_confront_Stackable l with "[$]").
    iIntros "%Hl ?".
    iDestruct (vmapsfrom_correct with "[$]") as "%Hy".
    iApply (wps_confront_vmapsfrom l with "[$]").
    { intros. destruct y; try easy.
      assert (qp ≠ 0)%Qz.
      { intros ?. destruct Hy; try easy. smultiset_solver. }
      rewrite (comm Qz_add).
      rewrite comm. apply Qz_lt_add_l. easy. }
    iIntros "(? & ? & %Hd)".
    wps_free l.
    { destruct y; set_solver. }

    iApply (wps_cleanup_vsingleton with "[$]"). iIntros "(? & ?)".
    iApply (wps_cleanup_singleton with "[$]"). iIntros "(? & _)".
    assert (({[+ l +]} ⊎ {[-l-]}) ≡ ∅) as -> by smultiset_solver.

    iDestruct ("Hf" with "[%] [$]") as "Hcall".
    { split; try easy. destruct Hy; try easy. smultiset_solver. }
    auto_locs.
    (* LATER mono + weak *)
    iApply (@wps_weak _ _ _ _ ({[f]} ∪ r)).
    { set_solver. }
    iApply (wps_mono with "[$]").

    iIntros (_) "? ?".
    iSpecialize ("IH" with "[] [$]").
    { iModIntro. iIntros (? ? ? ? ? ?) "%Hp ?".
      iApply "Hf"; last iFrame.
      iPureIntro. destruct Hp as [Hp ]. split; try easy.
      rewrite -app_assoc cons_middle in Hp. simpl in *. eauto. }
    iApply (@wps_mono with "[$]").

    iIntros (_) "(? & ?)".
    rewrite -app_assoc cons_middle. iFrame. }
Qed.

(* Can we derive other iter spec ? *)
Lemma destructive_iter_spec {A} r (I : list (A * (Qz * Qp)) -> iProp Σ) (R: A -> val -> iProp Σ) xs l f :
  □(∀ x y k qp qz s,
      ⌜xs = k ++ (x,(qz,qp))::s /\ (is_loc y -> qz ≠ 0%Qz)⌝ ∗
      y ↤?{qz} ∅ ∗ vStackable y qp ∗ ♢ 3 ∗ R x y ∗ I k -∗
      wps (Some ({[f]} ∪ r)) (call_clo (#f)%V [[y]])%T (fun _ => I (k ++ [(x,(qz,qp))]))) -∗
  ListOf R xs l ∗ I nil ∗ Stackable l 1%Qp ∗ l ↤ ∅ -∗
  wps (Some ({[f]} ∪ r)) (list_iter [[#f , l]])%T (fun _ => ♢ 1 ∗ I xs).
Proof.
  iIntros "#He ?".
  iApply (destructive_iter_spec_aux nil with "[] [$]").
  iModIntro.
  simpl. iIntros (? ? ? ? ? ?) "%Hp ?".
  destruct Hp.
  iApply "He". iFrame. eauto.
Qed.

(* LATER use in stacklist *)
Definition refList {A} (R: A -> val -> iProp Σ) xs r : iProp Σ :=
  ∃ l:loc, isRef l r ∗ ListOf R xs l ∗ Stackable l 1%Qp ∗ l ↤ {[+r+]} .

Lemma ref_cons_spec' {A} (R: A -> val -> iProp Σ) x qz xs r y :
  (is_loc y -> qz ≠ 0%Qz )->
  CODE (ref_cons [[y , #r]])
  SOUV ({[r]} ∪ locs y)
  PRE (♢ 3 ∗ refList R xs r ∗ R x y ∗ y↤?{qz} ∅)
  POST (fun _ => ∀ qp, vStackable y qp -∗ refList R ((x,(qz,qp))::xs) r).
Proof.
  iIntros (?) "(? & [%l (? & ? & ? & ?)] & ? & ?)".
  wps_call.
  wps_bind_nofree.
  wps_apply get_spec as "(%Hl & ?)". subst. iIntros. simpl.
  wps_bind.
  wps_apply list_cons_spec_debt as "(? & ? & Hl)". easy.
  wps_nofree.
  wps_apply @set_spec as "(? & ? & ?)". easy. iIntros.
  iSpecialize ("Hl" with "[$]").
  assert (opposite {[+ r +]}  ≡ {[-r-]}) as -> by smultiset_solver.
  rewrite left_id. iStepsS.
Qed.

Definition ref_cons_spec {A} (R: A -> val -> iProp Σ) (r l:loc) (vs:list val) (t:tm) (spec:iProp Σ) : iProp Σ :=
  ∀ x qz xs y,
    ⌜vs = [y]⌝ ∗
    ⌜is_loc y -> qz ≠ 0%Qz⌝ ∗ ♢ 3 ∗ refList R xs r ∗ R x y ∗ y↤?{qz} ∅ -∗
  wps (Some ({[r]} ∪ locs y)) t (fun _ => (∀ qp, vStackable y qp -∗ refList R ((x,(qz,qp))::xs) r) ∗ spec).
Local Instance lne_ref_cons_spec {A} (R: A -> val -> iProp Σ) r : LNE (ref_cons_spec R r).
Proof. lne. Qed.

Lemma prove_spec_ref_cons {A} (R: A -> val -> iProp Σ) (r l:loc) v :
  Spec 1 [((#r)%V, 1%Qz)] (ref_cons_spec R r) l -∗
  ref_cons_spec R r l [v] (ref_cons [[v, (#r)%V]])%T (Spec 1 [((#r)%V, 1%Qz)] (ref_cons_spec R r) l).
Proof.
  iIntros.
  iIntros (? ? ? ?) "(%Hv & %Hqz & ? & ? & ? & ?)".
  injection Hv. intros. subst.
  wps_apply (ref_cons_spec' R); last iFrame.
  eauto.
Qed.

Lemma list_rev_spec {A} (R: A -> val -> iProp Σ) xs l :
  CODE (list_rev [[l]])
  PRE (♢ 4 ∗ ListOf R xs l ∗ Stackable l 1%Qp ∗ l ↤ ∅)
  POST (fun l' => ♢ 4 ∗ ListOf R (List.rev xs) l' ∗ Stackable l' 1%Qp ∗ l' ↤ ∅).
Proof.
  iIntros "(? & Hlist & Hcl & Hmfl)".
  wps_call.
  simplify_substs.
  wps_bind.

  mine 1.
  wps_apply (list_nil_spec A R) as (l') "(Hl' & Hcv & Hml)".
  iIntros "Hcl".

  mine 1.
  rewrite (subst_not_in "acc"). 2:compute_done.
  wps_bind.
  wps_nofree.
  wps_apply (ref_spec 1%Qz ∅ l') as (r) "(Hr & Hmfl' & ? & ?)".
  { compute_done. }
  iIntros.
  wps_bind.
  wps_nofree. simpl.
  wps_apply (wps_mk_spec (ref_cons_spec R r) [("r", val_loc r)] [1 : Qz]).
  1-4:compute_done.
  { iModIntro. iIntros (? ?) "%Hl ?". do 2 (try destruct vs; try easy). simpl.
    iApply prove_spec_ref_cons.
    iFrame. }
  rew_qz. iFrame. simpl. iSplitR; first easy.
  iIntros (f) "(Hmf & ? & Hspec)". rewrite enc_loc.
  iIntros "(? & ?)".
  wps_bind.
  wps_context f.

  replace ({[f; r]}) with ({[r]} ∪ {[f]} : gset loc) by set_solver.
  wps_apply (destructive_iter_spec {[r]}
               (fun ys => Spec 1 [((#r)%V, 1%Qz)] (ref_cons_spec R r) f ∗
                         refList R (rev ys) r) R)%I.
  { iModIntro.
    iIntros (? ? ? ? ? ?) "(%Hp & ? & ? & ? & ? & (Hspec & ?))".
    destruct Hp.
    wps_context y.
    wps_call_spec as "Hspec".
    (* LATER mono_weak *)
    wps_mono "[-]".
    iApply @wps_weak.
    2:iApply "Hspec"; iFrame; eauto.
    set_solver.
    simpl. iIntros (_) "(Hkont & ?) ?".
    iSpecialize ("Hkont" with "[$]").
    rewrite rev_app_distr. simpl. iFrame. }
  simpl. rewrite left_id.
  iSplitR "Hmf". { iExists _. iFrame. }
  clear l'.
  iIntros (_) "(? & Hspec & [%l' (? & ? & ? & ?)] ) Hcf ?".
  iApply wps_end.

  wps_nofree.
  wps_apply @get_spec_enc as "(%Hv & Hr)". subst.

  wps_context l'.
  iApply wps_esupd.
  { set_solver. }
  { apply (spec_esupd_free f). }
  iFrame.

  iIntros "(? & (?& _))". simpl.

  iApply wps_esupd.
  { set_solver. }
  { apply (free_ref). }
  iFrame.
  iIntros "(? & ?)".

  do 2 iDestruct (diamonds_join with "[$]") as "?".
  iApply (wps_cleanup_singleton with "[$]").
  iIntros "(? & _)".
  assert (({[+ r +]} ⊎ {[-r-]}) ≡ ∅) as -> by smultiset_solver.
  wps_val. iIntros. rew_qz. iFrame.
Qed.
End HardIter.
