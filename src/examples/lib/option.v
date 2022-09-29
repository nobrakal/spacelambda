From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz smultiset.
From spacelambda.language Require Import notation.

From spacelambda Require Import more_space_lang wp_all wps triple.
From spacelambda.examples.tactics Require Import tactics.

(* We implement options as blocks of size 2, with a tag:
   + 0 if None
   + 1 if Some, and then the second field is relevant.
 *)

(******************************************************************************)
(* Actual specifications. *)

Definition option_none : val :=
  λ: [[]],
    let: "opt" := alloc ^2 in
    "opt".[0] <- 0;;
    "opt".[1] <- val_unit;;
    "opt".

Definition option_some : val :=
  λ: [["v"]],
    let: "opt" := alloc ^2 in
    "opt".[0] <- 0;;
    "opt".[1] <- "v";;
    "opt".

Definition option_is_none : val :=
  λ: [["opt"]],
    "opt".[0].

Definition option_get_some : val :=
  λ: [["opt"]],
    "opt".[1].

Section Option.
Context `{!interpGS Σ}.

Definition isOption (qn:Qz) (v:option val) (l:loc) : iProp Σ :=
  ∃ (tag:nat) (content:val),
    l ↦ BBlock [val_nat tag; content] ∗ ⌜match v with None => tag=0 | Some v => tag = 1 /\ content = v end⌝ ∗ content ↤?{qn} {[+l+]}.

Ltac destruct_option Ho :=
  iDestruct Ho as "[%tag [%context (? & %Hcon & ?)]]".

Lemma option_none_spec :
  CODE (option_none [[]])
  PRE  (♢ 2)
  POST (fun (l:loc) => isOption 1%Qz None l ∗ l ↤ ∅ ∗ Stackable l 1%Qp).
Proof.
  iIntros.
  wps_nofree.
  iStepsS.
Qed.

Lemma option_is_none_spec qn o l :
  CODE (option_is_none [[l]])
  PRE (isOption qn o l)
  POST (fun (n:nat) => ⌜n=0 <-> o=None⌝ ∗ isOption qn o l).
Proof.
  iIntros "Ho". destruct_option "Ho".
  iStepsS.

  destruct o.
  { destruct Hcon. split; intros; try easy; congruence. }
  { subst. split; eauto. }
Qed.

Lemma option_get_some_spec qn o l :
  CODE (option_get_some [[l]])
  PRE (isOption qn o l)
  POST (fun v' => ⌜match o with Some v => v=v' | None => True end⌝ ∗ isOption qn o l).
Proof.
  iIntros "Ho". destruct_option "Ho".
  iStepsS.
  destruct o; eauto; destruct Hcon; eauto.
Qed.

End Option.
