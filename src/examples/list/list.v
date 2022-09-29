From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.fracz Require Import qz qz_cmra smultiset_cmra.
From spacelambda.language Require Import notation.
From spacelambda Require Import interp.

From spacelambda Require Import more_space_lang wp_all wpc triple.

From spacelambda.examples.tactics Require Import tactics.
From spacelambda.examples.lib Require Export utils.

(* ------------------------------------------------------------------------ *)
(* Definition of lists and functions on them.
   In particular, we define ListOf, which abstracts the item, and
   List using ListOf.
 *)

Definition list_is_nil : val :=
  λ: [["l"]],
    let: "tag" := "l".[0] in
     1 '- "tag".

Definition list_head : val :=
  λ: [["l"]], "l".[1].

Definition list_tail : val :=
  λ: [["l"]], "l".[2].

Definition list_nil : val :=
  λ: [[]],
    let: "x" := alloc 1 in
    "x".[0] <- 0 ;;
    "x".

Definition list_cons : val :=
  λ: [["x","xs"]] ,
    let: "l" := alloc 3 in
    "l".[0] <- 1 ;;
    "l".[1] <- "x" ;;
    "l".[2] <- "xs";;
    "l".

Module ListsOf.

(* LATER reorder / beautify *)
(* LATER defs for tags *)
(* LATER Specialize the spec for one qz and one qp, the same for all elements. *)
Fixpoint ListOf `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) (xs : list (A * (Qz * Qp))) (l : loc) : iProp Σ :=
  match xs with
  | [] => l ↦ BBlock [ ^0 ]
  | (x,(qz,qp)) :: xs =>
    ∃ v l', l ↦ BBlock [ ^1; v; #l'] ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} {[+l+]} ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ ListOf R xs l'
end.

Lemma ListOf_eq `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) (xs : list (A * (Qz * Qp))) (l : loc) :
  ListOf R xs l = (match xs with
  | [] => l ↦ BBlock [ ^0 ]
  | (x,(qz,qp)) :: xs =>
      ∃ v l', l ↦ BBlock [ ^1; v; #l'] ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} {[+l+]} ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ ListOf R xs l' end)%I.
Proof. destruct xs; easy. Qed.

Lemma ListOf_nil `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) l :
  (l ↦ BBlock [ ^0 ])%I ≡ ListOf R nil l.
Proof. easy. Qed.
Lemma ListOf_cons `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) x qz qp xs l :
  (∃ v l', l ↦ BBlock [ ^1; v; #l'] ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} {[+l+]} ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ ListOf R xs l')%I ≡ ListOf R ((x,(qz,qp))::xs) l.
Proof. easy. Qed.

Lemma list_nil_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) :
  CODE (list_nil [[]])
  PRE (♢ 1)
  POST (fun (l:loc) => ListOf R [] l ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  repeat (iStepsS; wps_bind).
Qed.

(* This spec is a "debt" as, to recover the List predicate in post, the user has
   to cancel the mapsfrom given in arguments by giving the opposite. Thank you smultiset *)
(* We can still derive the usual spec, see below. *)

Lemma list_cons_spec_debt `{!interpGS Σ} A (R:A -> val -> iProp Σ) l qz r x v xs :
  (is_loc v -> qz ≠ 0%Qz) ->
  CODE (list_cons [[v,l]])
  SOUV (locs v)
  PRE  (♢ 3 ∗ ListOf R xs l ∗ Stackable l 1%Qp ∗ l ↤ r ∗ R x v ∗ v ↤?{qz} ∅)
  POST (fun (l':loc) => Stackable l' 1%Qp ∗ l' ↤ ∅ ∗ (∀ qp, vStackable v qp -∗ l ↤{0} (opposite r) -∗ ListOf R ((x,(qz,qp))::xs) l')).
Proof.
  iIntros (?) "(? & ? & ? & ? & ? & ?)".
  iStepsS.
  wps_nofree.
  iStepsS.

  assert (opposite r ⊎ (r ⊎ {[+ x0 +]}) ≡ {[+ x0 +]}) as -> by smultiset_solver.
  rewrite left_id.
  rew_set.
  iStepsS.
Qed.

Lemma list_cons_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) l qz qp x v xs :
  (is_loc v -> qz ≠ 0%Qz) ->
  CODE (list_cons [[v,l]])
  PRE  (♢ 3 ∗ ListOf R xs l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅)
  POST (fun (l':loc) => ListOf R ((x,(qz,qp))::xs) l' ∗ Stackable l' 1%Qp ∗ l' ↤ ∅).
Proof.
  iIntros (?) "(? & ? & ? & Hfl & ? & ? & ?)".
  wps_context v.
  iDestruct (mapsfrom_split_empty l 0 1 with "[Hfl]" ) as "[? ?]".
  { rewrite left_id_L. easy. }
  iDestruct (list_cons_spec_debt A R with "[$]") as "?".
  { easy. }
  iApply (@wps_mono with "[$]").
  iIntros (?) "(? & ? & Hf)". iFrame.
  iIntros.
  iApply ("Hf" with "[$]").
  assert (opposite ∅ ≡ ∅) as -> by set_solver.
  easy.
Qed.

Lemma list_is_nil_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) l vs :
  CODE (list_is_nil [[l]])
  PRE (ListOf R vs l)
  POST (fun (n:nat) => ⌜n ≠ 0 <-> vs = nil⌝ ∗ ListOf R vs l).
Proof.
  iIntros "Hl".
  wps_nofree.
  destruct vs as [|(?,(?,?))]; simpl.
  iStepsS. iStepsS.
Qed.

Definition Beheaded `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) v xs l : iProp Σ:=
  ∃ l', l ↦ BBlock [ ^1; v; #l'] ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ ListOf R xs l'.

Lemma list_head_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) l qz qp x xs :
  CODE (list_head [[l]])
  PRE  (ListOf R ((x,(qz,qp))::xs) l)
  POST (fun v => R x v ∗ v ↤?{qz} {[+l+]} ∗ vStackable v qp ∗ Beheaded R v xs l).
Proof. iStepsS. Qed.

(* LATER is there a better spec for tail ? *)
Lemma list_tail_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) v l xs :
  CODE (list_tail [[l]])
  PRE  (Beheaded R v xs l)
  POST (fun (l':loc) => ListOf R xs l' ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ l↦ BBlock [ ^1 ; v ; #l']%V).
Proof. iStepsS. Qed.

Lemma list_free `{!interpGS Σ} A (R:A -> val -> iProp Σ) l xs :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ ListOf R xs l =#=∗
  ♢(1+3*length xs) ∗ †l ∗
  ∃ vs, soup R ∅ xs vs.
Proof.
  revert l.
  induction xs as [|(x,(qz,qp)) vs]; intros l.
  { iIntros "(? & ? & ?)". iIntros.
    simpl.
    iMod (@logical_free with "[$] [$]") as "(? & ? & ?)"; try easy.
    rew_qz.
    iFrame. iExists nil. iApply soup_empty. }
  { iIntros "(? & ? & [%v [%l' (? & ? & ? & ? & ? & ? & ?)]])".
    iIntros (? ? ?) "Hi".
    fold (ListOf R vs l').
    iMod (@logical_free _ _ _ _ l with "[$] [Hi]") as "(? & ? & #Hl)"; try easy.
    { set_solver. }
    iMod (vmapsfrom_cleanup with "[$] [$]") as "(? & ? & ?)".
    iMod (mapsfrom_cleanup with "[$] [$]") as "(? & ?)".
    rewrite disj_union_sinlgeton_opposite.

    iMod (IHvs with "[$] [$]") as "(? & ? & ? & [%vs' ?])"; try easy.
    iFrame.
    iDestruct (diamonds_join with "[$]") as "Hdiams".
    iFrame "Hl". iModIntro.
    iSplitL "Hdiams".
    { conclude_diamonds. }
    { iExists (v::vs'). iFrame. } }
Qed.

Global Opaque ListOf.

End ListsOf.

Module Lists.
Import ListsOf.
Definition List `{!interpGS Σ} (xs:list (val*(Qz*Qp))) l : iProp Σ :=
  ListOf (fun x y => ⌜x=y⌝)%I xs l.

Lemma List_nil `{!interpGS Σ} l :
  (l ↦ BBlock [ ^0 ])%I ≡ List nil l.
Proof. easy. Qed.
Lemma List_cons `{!interpGS Σ} x qz qp xs l :
  (∃ l', l ↦ BBlock [ ^1; x; #l'] ∗ vStackable x qp ∗ x ↤?{qz} {[+l+]} ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ List xs l')%I ≡ List ((x,(qz,qp))::xs) l.
Proof.
  iSplit. iStepsS. iApply ListOf_cons. iStepsS.
  unfold List. rewrite -ListOf_cons. iStepsS.
Qed.

Lemma list_nil_spec `{!interpGS Σ} :
  CODE (list_nil [[]])
  PRE  (♢ 1)
  POST (fun (l:loc) => List [] l ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  iIntros.
  wps_apply (@list_nil_spec _ _ val (fun x y => ⌜x=y⌝)%I).
  iFrame.
Qed.

Lemma list_cons_spec `{!interpGS Σ} l qz qp v xs :
  (is_loc v -> qz ≠ 0%Qz) ->
  CODE (list_cons [[v,l]])
  PRE  (♢ 3 ∗ List xs l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗  vStackable v qp ∗ v ↤?{qz} ∅)
  POST (fun (l':loc) => List ((v,(qz,qp))::xs) l' ∗ Stackable l' 1%Qp ∗ l' ↤ ∅).
Proof.
  iIntros (?) "(? & ? & ? & ? & ? & ?)".
  wps_apply (@list_cons_spec _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Lemma list_is_nil_spec `{!interpGS Σ} l vs :
  CODE (list_is_nil [[l]])
  PRE  (List vs l)
  POST (fun (n:nat) => ⌜n ≠ 0 <-> vs = nil⌝ ∗ List vs l).
Proof.
  iIntros.
  wps_apply (@list_is_nil_spec _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Definition Beheaded `{!interpGS Σ} v xs l : iProp Σ:=
  ∃ l', l ↦ BBlock [ ^1; v; #l'] ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ List xs l'.

Lemma list_head_spec `{!interpGS Σ} l qz qp x xs :
  CODE (list_head [[l]])
  PRE  (List ((x,(qz,qp))::xs) l)
  POST (fun v => ⌜x=v⌝ ∗ v ↤?{qz} {[+l+]} ∗ vStackable v qp ∗ Beheaded v xs l).
Proof.
  iIntros.
  wps_apply (@list_head_spec _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Lemma list_tail_spec `{!interpGS Σ} v l xs :
  CODE (list_tail [[l]])
  PRE (Beheaded v xs l)
  POST (fun (l':loc) => List xs l' ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ l↦ BBlock [ ^1 ; v ; #l']%V).
Proof.
  iIntros.
  wps_apply (@list_tail_spec _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Lemma list_free `{!interpGS Σ} l xs :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ List xs l =#=∗
  ♢(1+3*length xs) ∗ †l ∗
  ∃ vs, soup (fun x y => ⌜x=y⌝)%I ∅ xs vs.
Proof.
  apply list_free.
Qed.
End Lists.

Module PaperLists.
Import Lists.

Definition List `{!interpGS Σ} (xs:list (val*Qp)) l : iProp Σ :=
  List (dupf <$> xs) l.

Lemma list_nil_spec `{!interpGS Σ} :
  CODE (list_nil [[]])
  PRE  (♢ 1)
  POST (fun (l:loc) => List [] l ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof. iIntros. wps_apply list_nil_spec. iFrame. Qed.

Lemma list_cons_spec `{!interpGS Σ} l qp v xs :
  CODE (list_cons [[v,l]])
  PRE  (♢ 3 ∗ List xs l ∗ Stackable l 1%Qp ∗ l ↤ ∅ ∗  vStackable v qp ∗ v ↤?{qp} ∅)
  POST (fun (l':loc) => List ((v,qp)::xs) l' ∗ Stackable l' 1%Qp ∗ l' ↤ ∅).
Proof.
  iIntros "(? & ? & ? & ? & ? & ?)".
  wps_apply list_cons_spec; eauto.
  intros. apply Qp_to_Qz_ne_zero.
Qed.

Lemma list_is_nil_spec `{!interpGS Σ} l vs :
  CODE (list_is_nil [[l]])
  PRE  (List vs l)
  POST (fun (n:nat) => ⌜n ≠ 0 <-> vs = nil⌝ ∗ List vs l).
Proof.
  iIntros.
  wps_apply list_is_nil_spec as "(% & ?)". iFrame. iPureIntro.
  destruct vs; naive_solver.
Qed.

Definition Beheaded `{!interpGS Σ} v xs l : iProp Σ:=
  ∃ l', l ↦ BBlock [ ^1; v; #l'] ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ List xs l'.

Lemma list_head_spec `{!interpGS Σ} l qp x xs :
  CODE (list_head [[l]])
  PRE  (List ((x,qp)::xs) l)
  POST (fun v => ⌜x=v⌝ ∗ v ↤?{qp} {[+l+]} ∗ vStackable v qp ∗ Beheaded v xs l).
Proof. iIntros. wps_apply list_head_spec. iFrame. Qed.

Lemma list_tail_spec `{!interpGS Σ} v l xs :
  CODE (list_tail [[l]])
  PRE (Beheaded v xs l)
  POST (fun (l':loc) => List xs l' ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ l↦ BBlock [ ^1 ; v ; #l']%V).
Proof.  iIntros. wps_apply list_tail_spec. iFrame. Qed.

Lemma list_free `{!interpGS Σ} l xs :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ List xs l =#=∗
  ♢(1+3*length xs) ∗ †l ∗
  ([∗ list] x ∈ xs, fst x ↤?{snd x:Qp} ∅ ∗ vStackable (fst x) (snd x)).
Proof.
  iIntros "(? & ? & ?)". iIntros.
  iMod (list_free with "[$] [$]") as "(? & ? & ? & [% ?])".
  rewrite fmap_length. iFrame. iModIntro.
  iApply soup_mixer. iFrame.
Qed.
End PaperLists.
