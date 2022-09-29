From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.spacelang Require Import stdpp hypotheses successors predecessors.
From spacelambda.language Require Import language.
From spacelambda.fracz Require Import qz.

From spacelambda Require Import more_maps_and_sets.
From spacelambda Require Import interp.

Section Cloud.

Context `{!interpGS Σ}.

(* ------------------------------------------------------------------------ *)

(* An open cloud [ocloud antecedents n ls] represents the ownership of a set
   of heap objects whose predecessors are contained in [antecedents], whose
   total size is [n], and whose addresses form the set [ls]. *)

Fixpoint ocloud (antecedents : gset loc) (n : nat) (locs : list loc) : iProp Σ
:=
  match locs with
  | [] =>
      ⌜ n = 0%nat ⌝
  | l :: locs' =>
      ∃ n' b,
        ⌜ n = (size_block b + n')%nat ⌝ ∗
        l ↦ b ∗
        mapsfrom_set l antecedents ∗
        Stackable l 1%Qp ∗
        ocloud antecedents n' locs'
  end%I.

(* A closed cloud is an open cloud whose domain is [locs] and whose
   antecedents are contained in [locs]. It is therefore closed under
   predecessors. *)

Definition cloud (locs : gset loc) n : iProp Σ :=
  ocloud locs n (elements locs).

Notation "locs ☁ n" :=
  (cloud locs n)
  (at level 20) : bi_scope.

(* ------------------------------------------------------------------------ *)

(* Auxiliary lemmas about clouds. *)

(* These two lemmas allow building clouds and are provided for use by an
   end user. *)

Lemma ocloud_empty antecedents :
  True ⊢ ocloud antecedents 0 [].
Proof.
  simpl ocloud. eauto.
Qed.

Lemma ocloud_cons antecedents n (locs : list loc) l b ls :
    ocloud antecedents n locs ∗ l ↦ b ∗ l ↤ ls ∗ Stackable l 1%Qp ∗
      ⌜ dom ls ⊆ antecedents ⌝
  ⊢ ocloud antecedents (size_block b + n) (l :: locs).
Proof.
  simpl ocloud. iIntros "(Hcloud & ? & ? & ? & %Hdom)".
  do 2 iExists _. rewrite /mapsfrom_set.
  iSplit; [ eauto |].
  iFrame. eauto.
Qed.

(* The following lemmas exploit a cloud and are used in the proof of the
   main lemma, [supd_free_group]. *)

Lemma ocloud_split antecedents (ls : list loc) : ∀ n,
  ocloud antecedents n ls ⊢
    ([∗ list] l ∈ ls, ∃ b, l ↦ b) ∗
    ([∗ list] l ∈ ls, Stackable l 1%Qp) ∗
  ([∗ list] l ∈ ls, mapsfrom_set l antecedents).
Proof.
  induction ls as [| l ls' IH ]; simpl ocloud; intro n.
  { iIntros "_". simpl. eauto. }
  { iIntros "H".
    iDestruct "H" as (n' b) "(? & ? & ? & ? & Hcloud)".
    rewrite IH. iDestruct "Hcloud" as "(? & ? & ?)".
    simpl. iFrame. iExists _. by iFrame. }
Qed.

Lemma cloud_split locs n :
  cloud locs n ⊢
  ([∗ set] l ∈ locs, ∃ b, l ↦ b) ∗
  ([∗ set] l ∈ locs, Stackable l 1%Qp) ∗
  ([∗ set] l ∈ locs, mapsfrom_set l locs).
Proof.
  iIntros "Hcloud".
  rewrite /cloud ocloud_split.
  rewrite big_opS_eq /big_opS_def.
  iFrame.
Qed.

Lemma ocloud_disjoint l b antecedents n (ls : list loc) :
  l ↦ b ∗ ocloud antecedents n ls ⊢ ⌜ l ∉ ls ⌝.
Proof.
  case (decide (l ∈ ls)); intro; [| eauto ].
  rewrite ocloud_split.
  iIntros "(Hl & Hls & _)".
  rewrite big_sepL_elem_of //.
  iDestruct "Hls" as (b') "?".
  iDestruct (gen_heap.mapsto_ne with "[$] [$]") as %Hneq.
  exfalso. eauto.
Qed.

Lemma gen_heap_valid_ocloud σ antecedents (ls : list loc) : ∀ n,
  gen_heap.gen_heap_interp σ ∗
  ocloud antecedents n ls -∗
  let locs := list_to_set ls in
  ⌜ locs ⊆ dom σ ∧
    (size_heap (deallocate locs σ) + n = size_heap σ)%nat ⌝.
Proof.
  induction ls as [| l ls' IH ]; simpl ocloud; intro n.
  { iIntros "(_ & %Hn)". iPureIntro. simpl.
    rewrite /deallocate gmap_mset_empty Hn.
    split. set_solver. lia. }
  { iIntros "(Hh & H)".
    iDestruct "H" as (n' b) "(%Hn & ? & ? & ? & Hcloud)".
    iDestruct (IH with "[$]") as "(%Hdom & %Hsize)".
    iDestruct (gen_heap.gen_heap_valid with "[$] [$]") as %Hl.
    assert (l ∈ dom σ) by eauto.
    iDestruct (ocloud_disjoint with "[$]") as "%Hdisj".
    iPureIntro. split; simpl.
    + set_solver.
    + rewrite -Hsize. rewrite Hn. rewrite /deallocate.
      rewrite -> gmap_mset_snoc' by eauto.
      rewrite Nat.add_assoc.
      rewrite size_heap_dealloc //.
      rewrite gmap_lookup_mset_outside //.
      set_solver. }
Qed.

Lemma exploit_cloud σ locs n :
  ph_interp σ ∗
  cloud locs n -∗
  ⌜ locs ⊆ dom σ ∧
    (size_heap (deallocate locs σ) + n = size_heap σ)%nat ⌝.
Proof.
  rewrite /ph_interp /cloud.
  iIntros "[(Hh & _) Hcloud]".
  iDestruct (gen_heap_valid_ocloud with "[$]") as "[%Hdom %Hsize]".
  iPureIntro.
  rewrite -> list_to_set_elements_L in Hdom, Hsize.
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Group deallocation. *)

(* This ghost operation consumes a closed cloud [locs☁n]. It produces a
   witness [††locs] that every location [l] in the set [locs] has been
   deallocated, and produces [n] space credits. *)

Lemma supd_free_group L locs n :
  locs ∩ L = ∅ ->
  locs☁n =[true | L]=∗ ††locs ∗ ♢n.
Proof.
  iIntros (?) "Hcloud".
  iIntros (? ? ?) "Hi".

  destruct_interp "Hi".
  (* The addresses [locs] must exist in the conceptual heap, and represent
     a total size of [n]. *)
  iDestruct (exploit_cloud with "[$]") as "[%Hdom %Hsize]".
  (* Deallocate [locs] in the conceptual heap. *)
  iDestruct (cloud_split with "[$]") as "(? & ? & ?)".

  iDestruct (exploit_Stackables_full with "[-]") as "%Hlocs".
  { iFrame. iExists _. iFrame. eauto. }

  iMod (ph_free_group θ locs with "[$]")
    as "(Hph & Hddag & %Hfacts)".

  set (θ' := deallocate locs θ).
  (* The available space in the heap increases by [n]. *)
  assert (Hspace: (available maxsize θ + n = available maxsize θ')%nat).
  { unfold available. destruct Hσ as [? _ _]. destruct Hθ as [? _ _].
    unfold valid_store in *.
    simpl in *. unfold θ'. lia. }
(*  assert (valid_state θ').
  { rewrite /valid_state. rewrite /valid_state in Hvalidθ. simpl. lia. } *)
  (* Perform a ghost update to create [n] new diamonds. *)
  iMod (ugfrac_update_incr _ _ n with "Hdiams") as "[Hauth Hfrag]".
  rew_qz.
  rewrite Hspace.
  fold (♢n)%I.
  (* Conclude. *)
  iModIntro. iFrame "Hddag Hfrag".
  (* Close the state interpretation invariant. *)
  iExists θ'. iFrame.
  iPureIntro. split_and !; eauto.
  { eapply free_group_preserves_correct; eauto. set_solver. }
  { eapply free_group_preserves_valid_store; eauto. }
  { eapply free_group_preserves_related; eauto. set_solver. }
Qed.

End Cloud.
