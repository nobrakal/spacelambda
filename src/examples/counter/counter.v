From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz qz_cmra smultiset_cmra.
From spacelambda.language Require Import notation closure.
From spacelambda Require Import interp.

From spacelambda Require Import utils more_space_lang wp_all wp_spec wps triple.

From spacelambda.examples.tactics Require Import tactics.
From spacelambda.examples.lib Require Import ref utils.

(* mk_counter returns a tuple of incr & get functions. *)
Definition mk_counter : val :=
  λ: [[]],
    let: "r" := ref [[0]] in
    let: "incr" := mk_clo BAnon [[]] (incr [["r"]]) in
    let: "get"  := mk_clo BAnon [[]] (get [["r"]]) in
    let: "b" := alloc 2 in
    "b".[0] <- "incr";;
    "b".[1] <- "get";;
    "b".

Section Counter.
Context `{!interpGS Σ}.

Definition get_clo_spec (r l:loc) (_:list val) (t:tm) (spec:iProp Σ): iProp Σ :=
  ∀ (n:nat), isRef n r -∗ wps (Some ∅) t (fun m => ⌜m=n⌝ ∗ isRef n r ∗ spec).
Local Instance lne_get_clo_spec r : LNE (get_clo_spec r).
Proof. lne. Qed.

Lemma prove_spec_get l env (vs:list val) r :
  length vs = 0 ->
  Spec 0 env (get_clo_spec r) l -∗
  get_clo_spec r l vs (get [[r]]%T) (Spec 0 env (get_clo_spec r) l).
Proof.
  iIntros. unfold get_clo_spec.
  iIntros.
  wps_nofree.
  wps_apply @get_spec_enc as "(%He & ?)".
  iFrame. easy.
Qed.

Definition incr_clo_spec (r l:loc) (_:list val) (t:tm) (spec:iProp Σ): iProp Σ :=
  ∀ (n:nat), isRef n r -∗ wps (Some ∅) t (fun (_:unit) => isRef (1+n) r ∗ spec).

Global Instance lne_incr_clo_spec r : LNE (incr_clo_spec r).
Proof. lne. Qed.

Lemma prove_spec_incr n (r l :loc) (qz:Qz) (vs : list val) :
  Spec n [(r:val, qz)] (incr_clo_spec r) l -∗
  incr_clo_spec r l vs (incr [[r]]%T) (Spec n [(r:val,qz)] (incr_clo_spec r) l).
Proof.
  iIntros. unfold incr_clo_spec.
  iIntros (?) "Hn". simpl.

  wps_apply incr_spec.
  iStepsS.
Qed.

(* The actual counter representation predicate. *)
Definition IsCounter (n:nat) (fi fg : loc) : iProp Σ :=
  ∃ r, isRef n r ∗ Stackable r 1%Qp ∗
         Spec 0 [((#r)%V,(1 / 2)%Qp : Qz)] (incr_clo_spec r) fi ∗
         Spec 0 [((#r)%V,(1 / 2)%Qp : Qz)] (get_clo_spec r) fg.

Lemma mk_counter_spec :
  CODE (mk_counter [])
  PRE (♢ 7)
  POST (fun l:loc =>
    (* We return a tuple *)
    ∃ fi fg:loc, l ↦ BBlock [val_loc fi;val_loc fg] ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗
    (* fi & fg are abstract locations. *)
    Stackable fi 1%Qp ∗ fi ↤ {[+l+]} ∗
    Stackable fg 1%Qp ∗ fg ↤ {[+l+]} ∗
    (* fi & fg form a counter. *)
    IsCounter 0 fi fg).
Proof.
  iIntros "Hdiams".
  wps_call. wps_bind.

  mine 1.
  wps_nofree.
  wps_apply ref_spec_no_loc as (r) "(Hr & Hrc & Hrmf)"; try easy.
  iDestruct (mapsfrom_split_empty r (1/2)%Qp (1/2)%Qp with "[Hrmf]") as "[Hrmf1 Hrmf2]".
  { rewrite -Qp_to_Qz_plus_distr Qp_half_half. replace (Qp_to_Qz 1%Qp) with 1%Qz. iFrame.
    compute_done. }

  wps_bind_nofree.

  mine 2.
  wps_apply (wps_mk_spec (incr_clo_spec r) [("r", val_loc r)] [(1/2)%Qp : Qz] ).
  1-4:compute_done.
  { iModIntro. iIntros. simpl. iApply prove_spec_incr. iFrame. }
  rew_qz. simpl. iFrame.
  iIntros (lincr) "(? & ? & Hi)".
  wps_bind.

  simplify_substs.
  mine 2.

  wps_nofree.
  wps_apply (wps_mk_spec (get_clo_spec r) [("r", val_loc r)] [(1/2)%Qp : Qz]).
  1-4:compute_done.
  { iModIntro. iIntros. simpl. iApply prove_spec_get; eauto. }
  rew_qz. simpl. iFrame.
  iIntros (lget) "(? & ? & Hg) ?". rewrite enc_loc.


  wps_bind_nofree.
  wps_alloc l as "(Hpt & ? & ? & ?)". simpl.
  do 2 (wps_bind_nofree; wps_store).
  wps_val. iIntros. iFrame.
  rewrite left_id.
  iExists lincr,lget.
  iFrame. iExists r. iFrame.
Qed.

Lemma counter_call_get (i:nat) fi fg :
  IsCounter i fi fg -∗
  wps (Some ∅) (call_clo fg []) (fun n:nat => ⌜i=n⌝ ∗ IsCounter i fi fg).
Proof.
  iIntros "[%r (Hr & Hfi & Hfg & Hspec)]".
  wps_call_spec as "Hspec".
  iFrame.
  unfold get_clo_spec.
  iSpecialize ("Hspec" with "[$]").

  iApply (@wps_mono with "[$]").

  iIntros (?) "(%Hv & ? & Hclo)".
  iSplitR; try easy.
  iExists r. iFrame.
Qed.

Lemma counter_call_incr (i:nat) fi fg :
  IsCounter i fi fg -∗
  wps (Some ∅) (call_clo fi []) (fun (_:unit) => IsCounter (1 + i) fi fg).
Proof.
  iIntros "[%r (Hr & Hfi & Hfg & ?)]".
  wps_call_spec as "Hspec".
  unfold incr_clo_spec.
  iSpecialize ("Hspec" with "[$]").

  iApply (wps_mono with "[$]").
  iIntros (v).
  iIntros "(? & Hclo)".
  iExists r. iFrame.
Qed.

Lemma counter_free i fi fg :
  IsCounter i fi fg ∗
  Stackable fi 1%Qp ∗ fi ↤ ∅ ∗
  Stackable fg 1%Qp ∗ fg ↤ ∅ =#=∗
  ♢ 5.
Proof.
  iIntros "([%ref (? & ? & Hfi & Hfg)] & fic & fif & fgc & fgf)".
  iIntros.
  iMod (spec_esupd_free  fi with "[$] [$]") as "(? & ? & Hs1)".
  simpl.
  iMod (@spec_esupd_free _ _ _ (get_clo_spec ref) with "[$] [$]") as "(Hi & Hk & ? & Hs2)".

  (* LATER lemma *)
  iDestruct "Hs1" as "(? & _)". simpl.

  iDestruct (mapsfrom_join with "[$] [$]") as "?".
  rew_qz.
  rewrite left_id.
  rewrite -Qp_to_Qz_plus_distr Qp_half_half.
  replace (1%Qp : Qz) with 1%Qz by compute_done.

  iDestruct (diamonds_join with "[$]") as "Hd".
  iMod (free_ref ref i with "[$] [$]") as "(? & ? & ?)".
  iFrame.
  iDestruct (diamonds_join with "[$]") as "Hd".
  rew_qz.
  by iFrame.
Qed.

End Counter.

Section PaperCounter.
Context `{!interpGS Σ}.

Lemma mk_counter_spec' :
  CODE (mk_counter [])
  PRE (♢ 7)
  POST (fun l:loc =>
    (* We return a tuple *)
    ∃ fi fg:loc, l ↦ BBlock [val_loc fi; val_loc fg] ∗ l ↩ ∅ ∗
    (* fi & fg are abstract locations. *)
    fi ↩ {[+l+]} ∗ fg ↩ {[+l+]} ∗
    (* fi & fg form a counter. *)
    IsCounter 0 fi fg).
Proof.
  iIntros.
  wps_apply mk_counter_spec as "[% [% (?&?&?&?&?)]]". rewrite !handle_one. iStepsS.
  rewrite !one_qp_qz. iStepsS. rewrite !one_qp_qz. iStepsS.
Qed.

Lemma counter_call_get' (i:nat) fi fg :
  CODE (call_clo fg [])
  PRE (IsCounter i fi fg)
  POST (fun n:nat => ⌜i=n⌝ ∗ IsCounter i fi fg).
Proof. apply counter_call_get. Qed.

Lemma counter_call_incr' (i:nat) fi fg :
  CODE (call_clo fi [])
  PRE (IsCounter i fi fg)
  POST (fun (_:unit) => IsCounter (1 + i) fi fg).
Proof. apply counter_call_incr. Qed.

Lemma counter_free' i fi fg :
  IsCounter i fi fg ∗ fi ↩ ∅ ∗ fg ↩ ∅ =[true | ∅]=∗ ♢ 5.
Proof.
  rewrite !handle_one.
  iIntros "(? & (?&?) & (?&?))". iIntros.
  simpl. iDestruct (counter_free i fi fg with "[$] [$]") as "?".
  by iFrame.
Qed.

End PaperCounter.
