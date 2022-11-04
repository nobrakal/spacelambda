From stdpp Require Import decidable binders gmultiset.
From iris Require Import proofmode.proofmode algebra.gmap.
From spacelambda Require Import language.notation more_space_lang wp_all triple.
From spacelambda.examples Require Import tactics utils diaframe vector.

Parameter time_credit_join : forall `{!interpGS Σ} (n m : nat),
  ($ n ∗ $ m -∗ $ (n + m)).

Parameter time_credit_split : forall `{!interpGS Σ} (n m : nat),
  ($ (n + m) -∗ $ n ∗ $ m).

Definition space_reserve (cap size : nat) : nat :=
  1 + size * 6 - cap.

Definition time_reserve (cap size : nat) : nat :=
  if decide (cap / 2 <= size) then
    (size - cap / 2) * 6
  else
    (cap / 2 - size) * 3.

Definition VectorAm `{!interpGS Σ} (vs : list (val * Qp)) (l : loc) : iProp Σ :=
  ∃ (capacity : nat),
      ⌜ capacity <= 1 `max` (4 * length vs) ⌝
    ∗ ♢ (space_reserve capacity (length vs))%nat
    ∗ $ (time_reserve capacity (length vs))
    ∗ Vector vs l capacity.

Lemma vector_create_amortized_spec `{!interpGS Σ} :
  CODE (vector_create [[]])
  PRE (♢ 4 ∗ $ 0)
  POST (fun (l:loc) => VectorAm [] l ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  iIntros "(Hdiams & T)".
  mine 4%nat as "dia".
  iPoseProof (vector_create_spec with "[dia]") as "A"; rew_qz; auto.
  iApply (wps_mono with "A").
  iDestruct (time_credit_split 0 with "[$]") as "(T0 & T)".
  iIntros (l) "(V & $ & $)".
  iFrame.
  iExists _; iFrame; simpl; auto.
Qed.

Lemma vector_size_amortized_spec `{!interpGS Σ} vs l :
  CODEFF (vector_size [[#l]])
  PRE (VectorAm vs l)
  POST (fun r : nat => ⌜r = length vs⌝ ∗ VectorAm vs l).
Proof.
  iIntros "V".
  iDestruct "V" as (l') "(? & ? & ? & V)".
  iPoseProof (vector_size_spec with "V") as "A".
  iApply (wps_mono with "A").
  iIntros (l'') "($ & ?)".
  iExists _; iFrame.
Qed.

Lemma space_reserve_push_no_resize cap size :
  cap <= 1 `max` (4 * size) ->
  6 + space_reserve cap size = space_reserve cap (size + 1).
Proof.
  unfold space_reserve; lia.
Qed.

Lemma time_reserve_push_no_resize cap size :
  time_reserve cap (size + 1) ≤ 6 + time_reserve cap size.
Proof.
  unfold time_reserve.
  do 2 destruct (decide _); lia.
Qed.

(** TODO consider transforming this into:
  ♢6 + ♢(reserve...) -∗ ♢(cap * 2) ∗ (♢cap -∗ ♢(reserve ...)) *)
Lemma space_reserve_push_resize cap :
  6 + space_reserve cap cap =
  cap * 2 + (space_reserve (cap * 2) (cap + 1) - cap).
Proof.
  unfold space_reserve.
  lia.
Qed.

Lemma time_reserve_push_resize size :
  7 + time_reserve size size =
    (1 + (size * 3 + 0)) + time_reserve (size * 2) (size + 1) + 3 * (size `mod` 2).
Proof.
  unfold time_reserve.
  rewrite Nat.div_mul //.
  pose proof Nat.div_mod_eq size 2.
  pose proof Nat.mod_upper_bound size 2.
  do 2 destruct (decide _); try lia.
Qed.

Lemma vector_push_amortized_spec `{!interpGS Σ} vs l v (q : Qp) :
  CODE (vector_push [[#l, v]])
  SOUV {[l]}
  PRE (vStackable v q ∗ v ↤?{q} ∅ ∗ VectorAm vs l ∗ ♢6 ∗ $7)
  POST (fun _ : () => VectorAm (vs ++ [(v, q)]) l).
Proof.
  iIntros "(Sv & pv & V & dia & T)".
  iDestruct "V" as (cap) "(%Ucap & dn & dT & V)".
  destruct (decide (length vs < cap)) as [ok|over].
  - (* size < cap: no resize *)
    wps_apply vector_push_spec_no_resize. auto.
    iDestruct select (_ ∗ _)%I as "(V & T)".
    (* re-establish invariant *)
    iExists cap.
    iFrame.
    iSplitR.
    + (* upper bound on cap *)
      iPureIntro. rewrite app_length. lia.
    + (* time and space credits *)
      iDestruct (diamonds_join with "[$]") as "?".
      rewrite app_length.
      rew_qz.
      rewrite space_reserve_push_no_resize // /=.
      iFrame.
      iDestruct (time_credit_join with "[$]") as "?".
      iApply (time_credit_weak with "[$]").
      apply time_reserve_push_no_resize.
  - (* size = cap: will resize *)
    iAssert ⌜length vs ≤ cap⌝%I as "%". by iDestruct "V" as (?) "(($ & _) & _ & _)".
    assert (cap = length vs) as -> by lia.
    wps_apply vector_push_spec_resize; auto.
    (* massaging credits to match precondition *)
    iDestruct (diamonds_join with "[$]") as "?".
    rew_qz.
    rewrite space_reserve_push_resize nat_to_Qz_add.
    iDestruct (diamonds_split with "[$]") as "(d2 & ?)".
    iDestruct (time_credit_join with "[$]") as "T".
    rewrite time_reserve_push_resize.
    iDestruct (time_credit_split_3 with "[$]") as "(T1 & T2 & Tjunk)".
    rew_qz. iFrame.
    iIntros (_) "(V & d & T0)".
    (* re-establish invariant *)
    iExists (length vs * 2).
    rewrite app_length.
    iFrame.
    iSplitR.
    + (* upper bound on cap *)
      iPureIntro. rew_qz. lia.
    + (* credits *)
      iDestruct (diamonds_join with "[$]") as "?".
      iApply (diamonds_eq with "[$]").
      rew_qz.
      rewrite /= // /space_reserve.
      lia.
Qed.

Lemma vector_set_amortized_spec `{!interpGS Σ} vs l i (x : val) (q : Qp) :
  i < length vs ->
  CODE (vector_set [[#l, ^i, x]])
  SOUV {[l]}
  PRE (vStackable x q
     ∗ x ↤?{q} ∅
     ∗ VectorAm vs l)
  POST (fun _ : () =>
       (let '(v,q) := vs !!! i in vStackable v q ∗ v ↤?{q} ∅ )
     ∗ VectorAm (<[i:=(x, q)]> vs) l).
Proof.
  iIntros (Hi) "(? & ? & V)".
  iDestruct "V" as (cap) "(%Hcap & ? & ? & V)".
  iPoseProof (vector_set_spec vs l cap i x with "[$]") as "A"; auto.
  iApply (wps_mono with "A").
  iIntros (?) "($ & V)".
  iExists cap; iFrame.
  rewrite insert_length.
  iSplitR; auto; iFrame.
Qed.

Lemma vector_get_amortized_spec `{!interpGS Σ} vs l i :
  i < length vs ->
  CODE (vector_get [[#l, ^i]])
  SOUV {[l]}
  PRE (VectorAm vs l)
  POST (fun r => ⌜r = (vs !!! i).1⌝ ∗ VectorAm vs l).
Proof.
  iIntros (Hi) "V".
  iDestruct "V" as (cap) "(%Hcap & ? & ? & V)".
  iPoseProof (vector_get_spec vs l cap i with "[$]") as "A"; auto.
  iApply (wps_mono with "A").
  iIntros (?) "($ & V)".
  iExists cap; iFrame.
  auto.
Qed.

Lemma space_reserve_pop_no_resize cap size :
  cap < 4 * size ->
  space_reserve cap (size + 1) = 6 + space_reserve cap size.
Proof.
  unfold space_reserve.
  lia.
Qed.

Lemma space_reserve_pop_resize cap size :
  cap ≤ 1 `max` (4 * (size + 1)) ->
  space_reserve cap (size + 1) =
    (1 `max` (size * 2)) +
      (((space_reserve (1 `max` (size * 2)) size) + 6) - cap).
Proof.
  unfold space_reserve.
  lia.
Qed.

Lemma time_reserve_pop_no_resize cap size :
  cap ≤ 1 `max` (4 * (size + 1)) ->
  cap < 4 * size ->
  3 + time_reserve cap (size + 1) =
  time_reserve cap size + if decide (cap `div` 2 ≤ size) then 9 else 0.
Proof.
  unfold time_reserve.
  pose proof Nat.div_mod_eq size 2.
  pose proof Nat.mod_upper_bound size 2.
  do 2 destruct (decide _); lia.
Qed.

Lemma time_reserve_pop_resize cap size :
  4 * size ≤ cap ->
  cap ≤ 1 `max` (4 * (size + 1)) ->
  4 + time_reserve cap (size + 1) >=
    (1 + (1 `max` (size * 2)) + (size + 0)) +
      time_reserve (1 `max` (size * 2)) size.
Proof.
  unfold time_reserve.
  pose proof Nat.div_mod_eq cap 2.
  pose proof Nat.mod_upper_bound cap 2.
  pose proof Nat.div_mod_eq (1 `max` (size * 2)) 2.
  pose proof Nat.mod_upper_bound (1 `max` (size * 2)) 2.
  do 2 destruct (decide _); lia.
Qed.

Lemma vector_pop_amortized_spec `{!interpGS Σ} vs l (x : val) (q : Qp) :
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (VectorAm (vs ++ [(x, q)]) l ∗ $4)
  POST (fun r => ⌜r = x⌝
      ∗ vStackable x q
      ∗ x ↤?{q} ∅
      ∗ VectorAm vs l
      ∗ ♢6).
Proof.
  iIntros "(V & T)".
  iDestruct "V" as (cap) "(%Ucap & dn & dT & V)".
  destruct (le_lt_dec (4 * length vs) cap) as [L|L].
  - (* cap >= 4*size, so resizing so that pop goes *)
    rewrite app_length in Ucap |- *; rew_qz.
    simpl length in *.
    (* credits necessary for pop *)
    rewrite space_reserve_pop_resize // nat_to_Qz_add.
    iDestruct (diamonds_split with "[$]") as "(dia & dn)".
    iDestruct (time_credit_join with "[$]") as "T".
    (* (throwing away a few time credits sometimes (0, 3, 6, or 8)) *)
    iDestruct (time_credit_weak with "[$]") as "T".
    now apply time_reserve_pop_resize; auto.
    iDestruct (time_credit_split with "[$]") as "(T1 & T)".
    wps_apply vector_pop_spec_resize; auto.
    iDestruct select (_ ∗ _)%I as "($ & $ & $ & V & dc & T0)".
    iDestruct (diamonds_join with "[$]") as "?".
    mine 6 as "dia".
    iFrame "dia".
    iExists _; iFrame.
    iSplitR.
    + iPureIntro. lia.
    + iApply (diamonds_eq with "[$]"). unfold space_reserve. rew_qz. lia.

  - (* cap < 4*size: no resize necessary *)
    rewrite app_length.
    wps_apply vector_pop_spec_no_resize; auto.
    iDestruct select (_ ∗ _)%I as "($ & $ & $ & V & T)".
    (* credits *)
    rewrite space_reserve_pop_no_resize // nat_to_Qz_add.
    iDestruct (diamonds_split with "[$]") as "($ & dn)".
    (* re-establish invariant *)
    iExists cap; iFrame.
    iDestruct (time_credit_join with "[$]") as "T".
    rewrite app_length in Ucap |- *.
    iSplitR.
    + iPureIntro. lia.
    + rewrite time_reserve_pop_no_resize //.
      iDestruct (time_credit_split with "[$]") as "($ & Tjunk)".
Qed.

Lemma vector_pop_amortized_spec_lookup `{!interpGS Σ} (vs : list (val * Qp)) l :
  vs ≠ [] ->
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (VectorAm vs l ∗ $4)
  POST (fun r =>
      let '(x, q) := vs !!! (length vs - 1) in
        ⌜r = x⌝
      ∗ vStackable x q
      ∗ x ↤?{q} ∅
      ∗ VectorAm (rev (tail (rev vs))) l
      ∗ ♢6).
Proof.
  intros Hvs.
  rewrite -(rev_involutive vs) in Hvs |- *.
  destruct (rev vs) as [ | (x, q) ? ]. tauto.
  iIntros "V".
  rewrite /= list_lookup_total_middle ?app_length ?Nat.add_sub //.
  iApply vector_pop_amortized_spec.
  iExactEq = "V". iPureIntro. do 3 f_equal.
  rewrite rev_app_distr /= rev_involutive //.
Qed.

Lemma vector_free_amortized  `{!interpGS Σ} vs l :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ VectorAm vs l =#=∗
  ♢(4 + 6 * length vs) ∗ †l
  ∗ ([∗ list] vq ∈ vs, let '(v,q) := vq in vStackable v q ∗ v ↤?{q} ∅).
Proof.
  iIntros "(Sl & Pl & V)".
  iIntros (? ? σ) "Hi".
  iDestruct "V" as (cap) "(%Ucap & dia & T & V)".
  iPoseProof (vector_free  vs l cap
               with "[$Sl $Pl $V] Hi")
    as ">(Hi & Sk & ? & ?)".
  iFrame.
  iDestruct (diamonds_join with "[$]") as "dia".
  iModIntro.
  iApply (diamonds_eq with "[$]").
  rew_qz.
  unfold space_reserve; lia.
Qed.
