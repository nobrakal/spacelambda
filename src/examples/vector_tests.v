From stdpp Require Import decidable binders gmultiset.
From iris Require Import proofmode.proofmode algebra.gmap.
From spacelambda Require Import language.notation more_space_lang wp_all triple.
From spacelambda.examples Require Import tactics utils diaframe vector.

(** Examples for non-amortized specifications *)

(** Cleanup tactic for proving examples *)

Import environments.
Local Ltac cleanup :=
  simpl;
  repeat (
      match goal with |- envs_entails _ (_ -∗ _) => iIntros "?" end
     || match goal with |- envs_entails _ (∀ _, _) => iIntros (?) end
     || match goal with |- envs_entails _ (♢ ?n ∗ _)%I => mine n as "_H"; [ iFrame "_H" | ..] end
     || iDestruct (diamonds_join with "[$]") as "?"
     || iDestruct select (_ ∗ _)%I as "(? & ?)"
     || iDestruct select (⌜_⌝)%I as "%").

Example example `{!interpGS Σ} :
  CODE (
      let: "v" := vector_create [[]] in
      vector_push [["v", ^1]];;
      vector_push [["v", ^2]];;
      vector_push [["v", ^3]];;
      vector_push [["v", ^4]];;
      vector_push [["v", ^5]];;
      vector_push [["v", ^6]];;
      vector_push [["v", ^7]];;
      vector_set [["v", ^0, ^11]];;
      vector_set [["v", ^1, ^12]];;
      vector_set [["v", ^1, ^22]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      let: "x" := vector_pop [["v"]] in
      "x"
    )
  PRE (♢19 ∗ $43)
  POST (fun res : val => ⌜res = 22⌝ ∗ ♢19 ∗ $0).
Proof.
  iIntros "?".
  cleanup.
  wps_bind. wps_apply vector_create_spec. cleanup.
  wps_bind. wps_apply vector_push_spec_no_resize; auto. cleanup.
  wps_bind. wps_apply vector_push_spec_resize; auto. simpl. cleanup.
  wps_bind. wps_apply vector_push_spec_resize; auto. simpl. cleanup.
  wps_bind. wps_apply vector_push_spec_no_resize; auto. cleanup.
  wps_bind. wps_apply vector_push_spec_resize; auto. simpl. cleanup.
  wps_bind. wps_apply vector_push_spec_no_resize; auto. cleanup.
  wps_bind. wps_apply vector_push_spec_no_resize; auto. cleanup.
  wps_bind. wps_apply vector_set_spec; auto. simpl; lia. cleanup.
  wps_bind. wps_apply vector_set_spec; auto. simpl; lia. cleanup.
  wps_bind. wps_apply vector_set_spec; auto. simpl; lia. cleanup.
  wps_bind. wps_apply vector_pop_joined_specs_lookup; auto. cleanup.
  wps_bind. wps_apply vector_pop_joined_specs_lookup; auto. cleanup.
  wps_bind. wps_apply vector_pop_joined_specs_lookup; auto. cleanup.
  wps_bind. wps_apply vector_pop_joined_specs_lookup; auto. cleanup.
  wps_bind. wps_apply vector_pop_joined_specs_lookup; auto. cleanup.
  wps_bind.
  iApply wps_context_singleton. iFrame.
  wps_apply vector_pop_joined_specs_lookup; auto. cleanup.
  iApply (wps_esupd _ _ _ _ (vector_free _ _ _)). iFrame. cleanup.
  subst. wps_val. iSplit; auto. rew_qz; auto. iFrame.
Unshelve.
  all: try exact 1%Qp.
  set_solver.
Qed.

(** Examples for amortized specifications *)

Tactic Notation "cleanup" :=
  simpl;
  repeat (
      match goal with |- envs_entails _ (_ -∗ _) => iIntros "?" end
     || match goal with |- envs_entails _ (∀ _, _) => iIntros (?) end
     || match goal with |- envs_entails _ (♢ ?n ∗ _)%I => mine n as "_H"; [ iFrame "_H" | ..] end
     || match goal with |- envs_entails _ ((♢ ?n ∗ _) ∗ _)%I => mine n as "_H"; [ iFrame "_H" | ..] end
     || match goal with |- envs_entails _ ($ ?n ∗ _)%I => iDestruct (time_credit_split_alt n with "[$]") as "($ & ?)"; [ try lia | ]  end
     || iDestruct (diamonds_join with "[$]") as "?"
     || iDestruct select (_ ∗ _)%I as "(? & ?)"
     || iDestruct select (⌜_⌝)%I as "%").

Example amortized_example `{!interpGS Σ} :
  CODE (
      let: "v" := vector_create [[]] in
      vector_push [["v", ^1]];;
      vector_push [["v", ^2]];;
      vector_push [["v", ^3]];;
      vector_push [["v", ^4]];;
      vector_push [["v", ^5]];;
      vector_push [["v", ^6]];;
      vector_push [["v", ^7]];;
      vector_set [["v", ^0, ^11]];;
      vector_set [["v", ^1, ^12]];;
      vector_set [["v", ^1, ^22]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      vector_pop [["v"]];;
      let: "x" := vector_pop [["v"]] in
      "x"
    )
  PRE (♢46 ∗ time_credit 73)
  POST (fun res : val => ⌜res = 22⌝ ∗ ♢46).
Proof.
  iIntros "?".
  wps_bind. wps_apply vector_create_amortized_spec. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_push_amortized_spec; auto. cleanup.
  wps_bind. wps_apply vector_set_amortized_spec. simpl; lia. cleanup.
  wps_bind. wps_apply vector_set_amortized_spec. simpl; lia. cleanup.
  wps_bind. wps_apply vector_set_amortized_spec. simpl; lia. cleanup.
  wps_bind. wps_apply vector_pop_amortized_spec_lookup. auto. cleanup.
  wps_bind. wps_apply vector_pop_amortized_spec_lookup. auto. cleanup.
  wps_bind. wps_apply vector_pop_amortized_spec_lookup. auto. cleanup.
  wps_bind. wps_apply vector_pop_amortized_spec_lookup. auto. cleanup.
  wps_bind. wps_apply vector_pop_amortized_spec_lookup. auto. cleanup.
  wps_bind.
  iApply wps_context_singleton; iFrame.
  wps_apply vector_pop_amortized_spec_lookup. auto. cleanup.
  iApply (wps_esupd _ _ _ _ (vector_free_amortized _ v)). iFrame. cleanup.
  wps_val. iSplit. auto. rew_qz. iFrame.
Unshelve.
  all: try exact 1%Qp.
  subst. auto.
Qed.
