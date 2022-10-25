From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import proofmode.

From spacelambda.spacelang Require Import hypotheses successors predecessors stdpp.
From spacelambda.spacelang Require iris.
From spacelambda.fracz Require Import qz qz_cmra smultiset fracset.
From spacelambda Require Import more_maps_and_sets.
From spacelambda Require Import tied.

(* This module sets-up the machinery needed for the store.
   It provides traditional points-to assertions through the Iris gen_heap:
   https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.gen_heap.html

   Moreover, a ghost mapping [π] of each memory location to its predecessors is maintained.
   In the user's eyes, this is done via "mapsfrom" assertion [l' ↤{q} ls]. The file's name,
   [ph], stands for "predecessor heap".

   These mapsfrom assertion are non-standard in two points:
   + First, predecessors are represented as signed multisets.
   + They can come with a null fraction, in that case with only a negative multiset.
     This property is enforced by fracset. *)

(* Suppose [L] is the type of memory locations, and [B] is the type of blocks
   stored in the heap, so the heap is a finite map of [L] to [B]. *)

(* ------------------------------------------------------------------------ *)

(* We want every memory location [l] to carry a ghost field [predecessors]
   that contains a multiset of locations: the predecessors of the location
   [l] in the heap. *)

(* Furthermore, we want to be able to split the ownership of this field,
   so that partial ownership of the [predecessors] field yields partial
   knowledge of the predecessors (and still allows updates), while full
   ownership of the [predecessors] field yields full knowledge of the
   predecessors. *)

(* Moreover, we want to generate some "permission to remove a location l
   from the multiset of predecessors". This is made possible using signed multisets
   with fraction zero. *)

(* These considerations lead us to using the following CMRA: *)

Notation predR L :=
  (authUR (gmapUR L (fracsetUR L))).

(* ------------------------------------------------------------------------ *)

(* This is our view of the heap. *)

Class phG L B Σ `{Countable L} := PhG {
  (* The heap, a mapping of locations to blocks. *)
  phG_heap :> gen_heapGS L B Σ;
  (* The predecessor resource, described above. *)
  phG_pred :> inG Σ (predR L);
  (* A ghost memory location that holds the predecessor mapping. *)
  phG_pred_name : gname;
}.

(* Make only the last argument explicit. *)
Arguments phG_pred      {L B Σ _ _} _ : assert.
Arguments phG_pred_name {L B Σ _ _} _ : assert.

(* ------------------------------------------------------------------------ *)

(* Assumptions and definitions. *)

Section ReasoningRules.

Context `{Countable L} {B : Type}.

Context `{Hypotheses L B}.

(* A heap [σ] is a finite map of locations to blocks. *)

Implicit Types σ : gmap L B.

(* A predecessor map [π] is a finite map of locations to multisets
   of locations. *)

Implicit Types π : gmap L (gmultiset L).

(* A signed predecessor map [μ] is a finite map of locations to signed
   multisets of locations. *)

Implicit Types μ : gmap L (fracset L).

(* We write [ls] and [ps] for signed multisets of locations. *)

Implicit Types ls ps : smultiset L.

(* We write [fs] for fracset. *)
Implicit Types fs : fracset L.

(* We write [fs] for gmultiset. *)
Implicit Types gs : gmultiset L.

(* We use [p] for non-null fractions *)
Implicit Types p : Qp.
(* We use [q] for possibly null fractions *)
Implicit Types q : Qz.

Notation dom := (dom (gset L)).

(* ------------------------------------------------------------------------ *)
(* A helper lemma *)
Lemma invariant_dom σ π :
  invariant σ π ->
  dom π ⊆ dom σ.
Proof. intros [[] ]. eauto. Qed.

(* ------------------------------------------------------------------------ *)

(* Our store interpretation predicate includes: 1- the standard store
   interpretation predicate [gen_heap_interp σ]; 2- the assertion [auth π],
   which represents the authoritative ownership of the ghost cell γ and
   holds the predecessor map π; 3- an invariant that ties [σ] and [π]. *)

Context `{ fG : !phG L B Σ }.

Notation own    := (@own Σ _ (phG_pred fG)).
Notation γ      := (phG_pred_name fG).

(* [pred σ π] asserts authoritatively the existence of all predecessors in π, plus
   some other fracsets in μ. All of these fracsets are tied, see tied.v . *)
Definition pred σ π : iProp Σ :=
  ∃ μ, ⌜tied σ π μ⌝ ∗ own γ (● ((full_gmultiset <$> π) ⋅ μ)).

(* The interpretation of the store: defines the authoritative assertions
   for mapsto (via gen_heap_interp) and mapsfrom (via pred) and links the two
   (via invariant) *)
Definition ph_interp σ : iProp Σ :=
  gen_heap_interp σ ∗
  ∃ π, pred σ π ∗ ⌜invariant σ π⌝.

(* ------------------------------------------------------------------------ *)

(* Notation for various forms of the pointsto assertion. *)

(* Fractional ownership of a memory block, where [q] is a fraction. *)

Notation "l ↦{ q } b" := (mapsto l (DfracOwn q) b)
  (at level 20, q at level 50, format "l  ↦{ q }  b") : bi_scope.

(* Full ownership of a memory block. *)

Notation "l ↦ b" := (l ↦{ 1%Qp } b)%I
  (at level 20) : bi_scope.

(* Persistent knowledge that a location has been deallocated. *)

Notation "† l" := (mapsto l DfracDiscarded deallocated)%I
  (at level 20) : bi_scope.

(* Persistent knowledge that a group of locations have been deallocated. *)

(* We use a set, as opposed to a multiset, because it seems inconvenient
   to have to deal with repeated elements here. *)

Notation "†† ls" := ([∗ set] l ∈ ls, †l)%I
  (at level 20) : bi_scope.

(* ------------------------------------------------------------------------ *)

(* Consequences of the [mapsto] assertion. *)

(* As usual, [l ↦{q} b] guarantees that the heap [σ] maps [l] to [b]. *)

Lemma exploit_mapsto σ l p b :
  ph_interp σ -∗ l ↦{p} b -∗ ⌜σ !! l = Some b⌝.
Proof.
  iIntros "[? _] ?".
  iDestruct (gen_heap_valid with "[$] [$]") as %?.
  eauto.
Qed.

(* [†l] guarantees that [l] has been freed. *)

Lemma exploit_discarded σ l :
  ph_interp σ -∗ †l -∗ ⌜ freed σ l ⌝.
Proof.
  iIntros "[? _] ?".
  iDestruct (gen_heap_valid with "[$] [$]") as %?.
  eauto.
Qed.

(* [††ls] guarantees that every location in [ls] has been freed. *)

Lemma exploit_discarded_group σ locs :
  ph_interp σ -∗ ††locs -∗ ⌜ ∀l, l ∈ locs → freed σ l ⌝.
Proof.
  (* By induction on the set [locs]. *)
  pattern locs. eapply set_ind_L; clear locs.
  (* Case: ∅. *)
  { iIntros. iPureIntro. intros l. rewrite elem_of_empty. tauto. }
  (* Case: {[l]} ∪ locs. *)
  { intros l locs ? IH.
    rewrite -> big_sepS_union by set_solver.
    rewrite big_sepS_singleton.
    iIntros "Hh [Hl Hlocs]".
    iDestruct (exploit_discarded σ l with "Hh Hl") as %?.
    iDestruct (IH with "Hh Hlocs") as %?.
    iPureIntro. set_solver. }
Qed.

(* ------------------------------------------------------------------------ *)

(* The predicate [mapsfrom l q ls] represents partial ownership of the
   ghost field [l.predecessors], and stores that the signed multiset [ls] is one
   share of the multiset [l.predecessors].
   As "one share" of a signed multiset is unclear, see [exploit_mapsfrom]
   for its formal meaning. *)

Definition mapsfrom l q ls : iProp Σ :=
  ∃ alln,
  own γ (◯ {[l := mk_nf q ls alln]}).

Notation "l ↤{ q } ls" :=
  (mapsfrom l q%Qz ls)
  (at level 20, format "l  ↤{ q }  ls")
: bi_scope.

Notation "l ↤ ls" :=
  (mapsfrom l 1%Qz ls)
  (at level 20, format "l  ↤  ls")
: bi_scope.

(* An abstraction of the previous assertion: in [mapsfrom_set l q ls],
   [ls] is a set, as opposed to a multiset. Thus, the multiplicity of
   each predecessor is unknown. *)

(* TODO propose a notation *)

Definition mapsfrom_set l locs : iProp Σ :=
  ∃ ps, l ↤{1%Qz} ps ∗ ⌜ dom ps ⊆ locs ⌝.

(* ------------------------------------------------------------------------ *)

(* The mapsfrom assertion is proper with respect to signed multisets. *)
Global Instance proper_mapsfrom x q : Proper (equiv ==> equiv) (mapsfrom x q).
Proof.
  intros X Y HXY.
  eapply bi.equiv_entails_2; iIntros "H"; iDestruct "H" as (pi) "H".
  - assert ({[x := mk_nf q X pi ]} ≡ {[x := mk_nf q Y (alln_upd HXY pi) ]}) as ->.
    { apply gmap_equiv_singleton.
      now constructor. }
    iExists _; iFrame.
  - symmetry in HXY.
    assert ({[x := mk_nf q Y pi ]} ≡ {[x := mk_nf q X (alln_upd HXY pi) ]}) as ->.
    { apply gmap_equiv_singleton.
      now constructor. }
    iExists _. iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* Combining two [mapsfrom] assertions. *)

Lemma mapsfrom_join l' q1 q2 ls1 ls2 :
  l' ↤{q1} ls1 -∗ l' ↤{q2} ls2 -∗
  l' ↤{q1+q2} (ls1 ⊎ ls2).
Proof.
  iIntros "[%a1 H1] [%a2 H2]".
  iCombine "H1 H2" as "H".
  iExists _. iFrame.
Qed.

(* Splitting a [mapsfrom] assertion.
   The precondition is richer, remember that we are working with fracset:
   if the fraction is null, then the support must be negative *)

Lemma mapsfrom_split l q ls q1 q2 ls1 ls2 :
  (q1 = 0%Qz -> AllNeg ls1) ->
  (q2 = 0%Qz -> AllNeg ls2) ->
  (q = q1 + q2)%Qz →
  ls ≡ ls1 ⊎ ls2 →
  l ↤{q} ls -∗
  l ↤{q1} ls1 ∗ l ↤{q2} ls2.
Proof.
  intros Hq1 Hq2 ? ->. intros. subst. iIntros "[%a H]".

  assert ({[l := mk_nf (q1 + q2)%Qz (ls1 ⊎ ls2) a]} ≡
            ({[l := mk_nf q1 ls1 Hq1]} ⋅ ({[l := mk_nf q2 ls2 Hq2]}))) as ->.
  { rewrite singleton_op.
    apply gmap_equiv_singleton.
    now constructor. }
  rewrite auth_frag_op own_op.
  iDestruct "H" as "[H1 H2]".
  iSplitL "H1"; iExists _; iFrame.
Qed.

(* A special case, when splitting a negative part *)
Lemma mapsfrom_split_neg ls1 ls2 l q ls :
 (q = 0%Qz -> AllNeg ls1) ->
  AllNeg ls2 ->
  ls ≡ ls1 ⊎ ls2 →
  l ↤{q} ls -∗
  l ↤{q} ls1 ∗ l ↤{0} ls2.
Proof.
  intros ? ? ->. apply mapsfrom_split; eauto.
  by rewrite right_id.
Qed.

(* The combination of the previous two lemmas. *)
Lemma mapsfrom_join_equiv l' q q1 q2 ls ls1 ls2 :
  (q1 = 0%Qz -> AllNeg ls1) ->
  (q2 = 0%Qz -> AllNeg ls2) ->
  (q1+q2)%Qz = q →
  ls1 ⊎ ls2 ≡ ls →
  l' ↤{q1} ls1 ∗ l' ↤{q2} ls2 ⊣⊢ l' ↤{q} ls.
Proof.
  intros ? ? ? <-. subst. iSplit.
  { iIntros "[H1 H2]".
    iDestruct (mapsfrom_join with "H1 H2") as "H". iFrame. }
  { iApply mapsfrom_split; eauto. }
Qed.

(* The special case where all multisets are empty. *)

Lemma mapsfrom_split_empty l q1 q2 :
  l ↤{q1} ∅ ∗ l ↤{q2} ∅ ⊣⊢ l ↤{q1 + q2} ∅.
Proof.
  now apply mapsfrom_join_equiv.
Qed.

(* Joining and splitting again. *)

Lemma mapsfrom_join_split l' q1 q2 ls1 ls2 ms1 ms2 :
  (q1 = 0%Qz -> AllNeg ms1) ->
  (q2 = 0%Qz -> AllNeg ms2) ->
  ls1 ⊎ ls2 ≡ ms1 ⊎ ms2 →
  l' ↤{q1} ls1 -∗ l' ↤{q2} ls2 -∗
  l' ↤{q1} ms1  ∗ l' ↤{q2} ms2.
Proof.
  intros ? ? E. iIntros "H1 H2".
  iDestruct (mapsfrom_join with "H1 H2") as "?". rewrite E.
  now iApply mapsfrom_split.
Qed.

(* We can always weaken a mapsfrom assertion. *)
Lemma mapsfrom_weak ls1 ls2 l q :
  (q = 0%Qz -> AllNeg ls2) ->
  (* NB this is not inclusion of signed multisets. *)
  (* TODO notation <= *)
  (forall x, multiplicity x ls1 <= multiplicity x ls2)%Z ->
  l ↤{q} ls1 -∗
    l ↤{q} ls2.
Proof.
  iIntros (? ?) "?".
  iDestruct (mapsfrom_split_neg ls2 (ls1 ⊎ opposite ls2) with "[$]") as "[? ?]"; eauto.
  all:smultiset_solver.
Qed.

Lemma mapsfrom_correct l q ls :
  l ↤{q} ls -∗ ⌜q = 0%Qz -> AllNeg ls⌝.
Proof.
  iIntros "[%E ?]". easy.
Qed.

(* ------------------------------------------------------------------------ *)

(* Basic facts about †l and ††ls. *)

Goal ∀ l, Persistent (†l).
Proof. typeclasses eauto. Qed.

Goal ∀ locs, Persistent (††locs).
Proof. typeclasses eauto. Qed.

Lemma ddag_singleton l :
  †l ⊣⊢ ††{[l]}.
Proof.
  rewrite big_sepS_singleton. eauto.
Qed.

Lemma ddag_join locs1 locs2 locs :
  locs1 ∪ locs2 = locs →
  ††locs1 ∗ ††locs2 ⊣⊢ ††locs.
Proof.
  intros. subst locs.
  rewrite !big_sepS_forall.
  eapply bi.equiv_entails_2.
  + iIntros "[H1 H2]" (l).
    rewrite elem_of_union.
    iIntros "%Hl". destruct Hl.
    - by iApply "H1".
    - by iApply "H2".
  + iIntros "#H".
    iSplit; iIntros (l) "%Hl"; iApply "H"; iPureIntro; set_solver.
Qed.

Lemma ddag_repeatm l n : †l -∗ ††dom (repeatm l n).
Proof.
  induction n.
  - rewrite gmultiset_dom_empty. auto.
  - rewrite dom_union.
    rewrite <-ddag_join. 2:reflexivity.
    iIntros "dl".
    iDestruct (bi.persistent_sep_dup with "dl") as "(dl & dl_)".
    iSplitL "dl".
    rewrite dom_singleton.
    + now iApply ddag_singleton.
    + now iApply IHn.
Qed.

(* ------------------------------------------------------------------------ *)

(* Exploiting an exact [mapsfrom] assertion. *)

Lemma option_included_Some_l_unital `{A:ucmra} (x:A) (y:option A) :
  Some x ≼ y -> exists y', y = Some y' /\ x ≼ y'.
Proof.
  intros Hx.
  apply option_included in Hx. destruct Hx as [|(a,(b,(Ha&?&Ho)))]; subst; try easy.
  injection Ha; intros ->.
  eexists. split; try easy.
  destruct Ho; try easy.
  exists ε. rewrite right_id //.
Qed.

Lemma exploit_frac_null μ fs q l :
  q = frac fs ->
  all_neg μ ->
  Some fs ≼ μ !! l ->
  q = 0%Qz.
Proof.
  intros ? Hn Hleq; subst.
  apply (@option_included_Some_l_unital (nfracUR (@smultisetUR L _ _))) in Hleq.
  destruct Hleq as (nfr,(Hin&Hleq)).
  assert (frac nfr = 0%Qz) as Hq' by eauto.
  apply nfrac_frac_le in Hleq.
  apply Qz_le_zero.
  rewrite -Hq' //.
Qed.

(* This is a very precise storement, unveiling μ. Use it at your own risk. *)
Lemma exploit_mapsfrom_precise σ π q l ls :
  dom π ⊆ dom σ ->
  q <> 0%Qz ->
  pred σ π -∗
  mapsfrom l q ls -∗
  ∃ μ gs ns,
    ⌜ tied σ π μ /\ π !! l = Some gs /\ μ !! l = Some ns /\
      (q = 1%Qz -> (of_gmultiset gs ⊆ (ls ⊎ opposite (supp ns)))) ⌝
     ∗ own γ (● ((full_gmultiset <$> π) ⋅ μ)) ∗ mapsfrom l q ls.
Proof.
  iIntros (Hinv Hq) "[%μ [%Hμ Hauth]] Hfrag".
  iDestruct "Hfrag" as (pr) "Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "%Hv".

  assert (exists gs ns, π !! l = Some gs /\ μ !! l = Some ns
                   /\ (q=1%Qz -> of_gmultiset gs ⊆ (ls ⊎ opposite (supp ns)))) as (ps,(ns,?)).
  2:{ iExists _, _,_. iFrame. iSplitR "Hfrag"; try iExists _; eauto. }

  (* Confront the authoritative element and the fragmentary element. *)
  apply auth_both_valid_discrete in Hv. destruct Hv as [Hv _].

  (* Perform lots of destruction. *)
  rewrite singleton_included_l in Hv.
  destruct Hv as [y [Hlookup Hord]].

  rewrite Some_included_total in Hord.
  rewrite lookup_op lookup_fmap in Hlookup.

  destruct Hμ as [Hdμ Hneg Hcovers].

  (* We can only be in π, therefore in μ *)
  destruct (π !! l) as [|] eqn:Hπl.
  { assert (l ∈ dom π) by (eauto with in_dom).
    assert (exists ns, μ !! l = Some ns) as (ns,Hμl).
    { apply elem_of_dom. rewrite Hdμ. set_solver. }
    rewrite Hμl.
    eexists _,_. do 2 (split; try easy).

    rewrite Hμl -Some_op in Hlookup.
    rewrite inj_iff in Hlookup.

    specialize (Hcovers l).
    rewrite Hπl Hμl in Hcovers.
    specialize (Hneg l _ Hμl).
    simpl in *.

    assert (frac y = 1%Qz) as Hy.
    { apply nfrac_equiv_frac in Hlookup.
      simpl in Hlookup. rewrite Hneg right_id // in Hlookup. }

    apply nfrac_equiv_supp in Hlookup. simpl in *.
    intros ->.
    apply from_full in Hord; last easy.
    destruct Hord as (z,(Hz1&Hz2&Hz3)).
    rewrite Hz1 in Hlookup. simpl in *.
    smultiset_solver. }
  { exfalso. simpl in Hlookup. rewrite left_id in Hlookup.
    apply Hq.
    eapply (exploit_frac_null μ); try easy; last first.
    erewrite Hlookup. by apply (@Some_included_2).
    easy. }
Qed.

(* [freeds σ gs] asserts that all the locations in gs are freed in σ *)
Definition freeds σ gs :=
  forall l, l ∈ gs -> freed σ l.

Lemma abstract_all_freeds σ π μ l gs ns ls:
  π !! l = Some gs ->
  μ !! l = Some ns ->
  freed_intersection σ π μ ->
  of_gmultiset gs ⊆ ls ⊎ opposite (supp ns) ->
  ∃ gs', gs ⊆ to_gmultiset ls ⊎ gs' ∧ freeds σ gs'.
Proof.
  intros Hπl Hμl Hco ?.
  exists (to_gmultiset (opposite (supp ns))).
  split.
  { smultiset_solver. }
  { intros i Hi.
    specialize (Hco l).
    rewrite Hπl Hμl in Hco. apply Hco.
    smultiset_solver. }
Qed.

(* When confronted with the authoritative assertion [pred σ π], the assertion
   [mapsfrom_exact l' q ls] guarantees that [l'] is in the domain of [π].
   Furthermore, if [q] is 1, then it guarantees that [predecessors π l'] is a subset
   of [ls] plus some deallocated locations. *)
Lemma exploit_mapsfrom σ π l q ls :
  q <> 0%Qz ->
  dom π ⊆ dom σ ->
  pred σ π -∗
  mapsfrom l q ls -∗
  ⌜ ∃ gs, π !! l = Some gs
      ∧ (q = 1%Qz → ∃ gs', gs ⊆ to_gmultiset ls ⊎ gs' ∧ freeds σ gs') ⌝.
Proof.
  iIntros (Hq Hinv) "? ?".
  iDestruct (exploit_mapsfrom_precise with "[$] [$]") as "[%μ [%gs [%ns [%Hmf ?]]]]".
  1,2:easy.
  iPureIntro.
  destruct Hmf as ([]&?&?&?).
  eauto using abstract_all_freeds.
Qed.

(* A simplified corollary of the previous lemma. *)

Lemma exploit_mapsfrom_dom σ π l' q ls :
  q <> 0%Qz ->
  dom π ⊆ dom σ ->
  pred σ π -∗
  l' ↤{q} ls -∗
  ⌜ l' ∈ dom π ⌝.
Proof.
  iIntros.
  iDestruct (exploit_mapsfrom with "[$] [$]") as %(? & Heq & ?);
    rewrite ?elem_of_dom ?Heq; eauto.
Qed.

Lemma exploit_mapsfrom_dom_large σ l' q ls :
  ph_interp σ -∗
  l' ↤{q} ls -∗
  ⌜ l' ∈ dom σ ⌝.
Proof.
  iIntros "[_ [%π [[%μ [%Htied Hμ]] %Hinv]]] [%a ?]".
  assert (dom π ⊆ dom σ) by (eauto using invariant_dom).
  destruct Htied as [Hd Hn _].
  iDestruct (own_valid_2 with "Hμ [$]") as "%Hv".
  iPureIntro.
  destruct (decide (l' ∈ dom σ)); try easy.
  exfalso.
  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv&_).
  rewrite lookup_included in Hv.
  specialize (Hv l').
  assert (μ !! l' = None) as Hμ.
  { apply not_elem_of_dom. now rewrite Hd. }
  assert (π !! l' = None) as Hπ.
  { apply not_elem_of_dom. set_solver. }
  rewrite lookup_op lookup_singleton lookup_fmap Hμ Hπ left_id_L in Hv.
  apply is_Some_included in Hv.
  { inversion Hv. easy. }
  { easy. }
Qed.

(* ------------------------------------------------------------------------ *)

(* Confronting a [mapsfrom] assertion and a deallocation witness. *)

Lemma exploit_mapsfrom_dag σ l' q ls :
  q <> 0%Qz ->
  ph_interp σ ∗ l' ↤{q} ls ∗ †l' ⊢ False.
Proof.
  intros Hq.
  iIntros "(Hh & Hmapsfrom & Hdag)".
  (* The location [l'] has been freed. *)
  iDestruct (exploit_discarded σ l' with "Hh Hdag") as "%Hfreed".
  iClear "Hdag".
  (* Unfold [ph_interp] to obtain [pred π]. *)
  unfold ph_interp.
  iDestruct "Hh" as "(_ & Hh)".
  iDestruct "Hh" as (π) "(Hpred & %Hinv)".
  (* Exploit the [mapsfrom] hypothesis. *)
  iDestruct (exploit_mapsfrom _ π l' q ls with "Hpred Hmapsfrom") as %Hm; try easy.
  { eauto using invariant_dom. }
  destruct Hm as (ps & Hπl' & _).
  (* Conclude. [l'] has been freed, so cannot be in the domain of [π].
     Contradiction. *)
  iPureIntro.
  assert (l' ∈ dom π) by eauto with in_dom.
  destruct Hinv as (Hco & _ & _).
  unfold coincidence in Hco.
  destruct Hco as (Hco & _).
  unfold coincidence_direct_freed in Hco.
  assert (l' ∉ dom π) by eauto.
  tauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* More lemmas on mapsfrom *)

Lemma mapsfrom_confront l1 q1 ls1 l2 q2 ls2 :
  (1 < q1 + q2)%Qz -> l1 ↤{q1} ls1 -∗ l2 ↤{q2} ls2 -∗ ⌜l1 ≠ l2⌝.
Proof.
  iIntros (Hlt) "[% ?] [% ?]". rewrite Qz_lt_nge in Hlt.
  iDestruct (own_valid_2 with "[$] [$]") as "%Hv".
  iPureIntro. intros ?. apply Hlt. subst.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
  destruct Hv as (Hv & ?). simpl in *.
  rewrite gfrac_valid in Hv.
  rewrite comm_L. easy.
Qed.

(* ------------------------------------------------------------------------ *)

(* Helper lemma for [pred_alloc]*)
Lemma alloc_fracset_local_update π μ l fs :
  frac fs = 1%Qz ->
  supp fs = ∅ ->
  (<[l:=fs]> ((full_gmultiset <$> π) ⋅ μ), ε : gmap L (fracset L)) ~l~>
  ((full_gmultiset <$> <[l:=∅]> π) ⋅ <[l:=ε]> μ, ε).
Proof.
  intros ? Hfs.
  apply local_update_unital_discrete.
  intros z Hv Hz.
  split.
  { apply prove_gmap_valid. intros ? ?.
    rewrite lookup_union_with lookup_fmap.
    destruct (decide (l=i)); subst.
    { rewrite !lookup_insert. simpl. injection 1. intros <-. easy. }
    { specialize (Hv i). rewrite !lookup_insert_ne //.
      rewrite !lookup_insert_ne // lookup_op lookup_fmap in Hv.
      intros Eq. rewrite -Some_valid -Eq. easy. } }
  rewrite left_id in Hz.
  rewrite -Hz left_id.
  intros x.
  rewrite lookup_union_with lookup_fmap.
  destruct (decide (x=l)); subst; simplify_map_eq.
  { do 2 constructor; simpl.
    { rewrite right_id //. }
    { rewrite ?Hfs; easy. } }
  { by rewrite lookup_union_with lookup_fmap. }
Qed.

(* The authoritative assertion [pred σ π] allows allocation: provided [l] is
   fresh, it can be changed to [pred σ (<[l:=∅]> π)], while producing [l ↤ ∅],
   which witnesses the fact that a newly allocated location has no
   predecessors. *)
Lemma pred_alloc σ π l b :
  l ∉ dom σ →
  b <> deallocated ->
  dom π ⊆ dom σ ->
  pred σ π ==∗
  pred (<[l:=b]> σ) (<[l:=∅]> π) ∗ l ↤ ∅.
Proof.
  intros.
  assert (Hπl: π !! l = None) by (eapply not_elem_of_dom; eauto).
  iIntros "[%μ [%Hμ Hauth]]".
  iMod (own_update with "Hauth") as "[Hauth Hfrag]".
  { eapply auth_update_alloc.
    eapply alloc_singleton_local_update with (i := l) (x := mk_nf 1 ∅ (fun _ => AllNeg_empty)); try easy.
    apply not_elem_of_dom.
    destruct Hμ as [Hd ? ?].
    rewrite dom_union_with dom_fmap_L Hd.
    set_solver. }
  iSplitL "Hauth"; last first.
  { iExists _. eauto. }
  iExists _. iSplitR.
  { eauto using tied_alloc. }
  iApply (own_update with "[$]").
  eapply auth_update_auth.
  now apply alloc_fracset_local_update.
Qed.

(* An interesting lemma. Under the right hypotheses,
   we can delete a location from π and transfer the negative part in μ *)
Lemma dealloc_fracset_update π μ l fs gs (ns:fracset L) :
  all_neg μ ->
  frac fs = 1%Qz ->
  π !! l = Some gs ->
  μ !! l = Some ns ->
  of_gmultiset gs ⊆ supp fs ⊎ opposite (supp ns) ->
  ((full_gmultiset <$> π) ⋅ μ, {[l := fs]}) ~l~>
  ((full_gmultiset <$> delete l π) ⋅ <[l:=null_neg_part (opposite (supp fs ⊎ opposite (supp ns) ⊎ opposite (of_gmultiset gs))) ]> μ, {[l := ε]}).
Proof.
  intros Hμ Hffs Hns Hπl ?.
  apply local_update_unital_discrete.
  intros z Hv Hz.
  split.
  { apply prove_gmap_valid. intros ? ?.
    rewrite lookup_op lookup_fmap.
    destruct (decide (l=i)); subst.
    { rewrite lookup_delete lookup_insert. injection 1. intros <-. easy. }
    { rewrite lookup_delete_ne // lookup_insert_ne //.
      intros Hv'. rewrite -Some_valid -Hv'.
      specialize (Hv i). rewrite lookup_op lookup_fmap // in Hv. } }
  intros x.
  specialize (Hz x).
  do 2 rewrite lookup_op in Hz. rewrite lookup_fmap in Hz.
  do 2 rewrite lookup_op. rewrite lookup_fmap.
  destruct (decide (l=x)); subst.
  { rewrite lookup_insert lookup_delete. simpl.

    rewrite lookup_insert Hπl Hns in Hz. simpl in Hz.
    rewrite -Some_op in Hz.
    rewrite lookup_singleton.

    assert (frac ns = 0%Qz) as Hfracns by eauto.

    destruct (z !! x) as [zx|] eqn:E; rewrite E.
    { rewrite -Some_op. constructor. rewrite left_id.
      rewrite E -Some_op inj_iff in Hz.

      inversion Hz as [Hf Hs]. simpl in *. clear Hz.
      rewrite Hffs Hfracns right_id in Hf.
      apply  Qz_add_eq_same in Hf.
      constructor; try easy; simpl.
      assert (supp zx ≡ opposite (supp fs ⊎ opposite (supp ns) ⊎ opposite (of_gmultiset gs) )) as Hs'.
      { smultiset_solver. }
      rewrite negative_part_AllNeg.
      { smultiset_solver. }
      { rewrite -Hs'. now apply neglz. } }
    { rewrite E right_id inj_iff in Hz.
      rewrite right_id left_id inj_iff.
      inversion Hz as [? Hs].
      constructor; try easy; simpl in *.
      rewrite negative_part_AllNeg; smultiset_solver. } }
  { rewrite lookup_delete_ne //.
    rewrite lookup_insert_ne // lookup_singleton_ne // left_id.
    rewrite lookup_singleton_ne // left_id in Hz.
    easy. }
Qed.

(* Conversely, the conjunction [pred σ π ∗ l ↤ ls] allows deallocation,
   and produces a witness that the predecessors of [l] form a subset
   of [ls] plus some deallocated locations [gs]. *)
Lemma pred_free_singleton σ π l ls :
  dom π ⊆ dom σ ->
  pred σ π -∗ l ↤ ls ==∗
  pred σ (delete l π) ∗ ⌜ exists gs, predecessors π l ⊆ to_gmultiset ls ⊎ gs /\ freeds σ gs ⌝.
Proof.
  iIntros (?) "Hauth Hpred".
  iDestruct (exploit_mapsfrom_precise _ π with "Hauth Hpred")
    as "[%μ [%ps [%ns [%Hpre [Hauth Hpred]]]]]"; try easy.
  destruct Hpre as (Hti&Hπl&Hμl&Hincl).
  specialize (Hincl eq_refl).
  assert (predecessors π l = ps) as -> by rewrite /predecessors Hπl //.
  iSplitL; last (destruct Hti; eauto using abstract_all_freeds).
  iDestruct "Hpred" as (alln) "Hpred".

  iExists _. iSplitR; last first.
  { iAssert (|==> own γ (● ((full_gmultiset <$> delete l π) ⋅ <[l:=null_neg_part (opposite (ls ⊎ opposite (supp ns) ⊎ opposite (of_gmultiset ps)))]> μ)) ∗ own γ (◯ {[l := ε]}))%I with "[Hauth Hpred]" as ">[? ?]".
    2:{ by iFrame. }

    rewrite -own_op.
    iApply (own_update_2 with "[Hauth] [Hpred]"). 2,3:iFrame.
    apply auth_update.
    destruct Hti.
    now eapply dealloc_fracset_update. }
  { eauto using tied_dealloc. }
Qed.

(* An iterated version of the previous lemma. *)

Lemma pred_free_group antecedents locs : ∀ σ π,
  dom π ⊆ dom σ ->
  pred σ π ∗
  ([∗ set] l ∈ locs, mapsfrom_set l antecedents)
  ==∗
  pred σ (gmap_mdelete locs π) ∗
  ⌜ exists gs, freeds σ gs /\ (∀ l l', l' ∈ locs → l ∈ predecessors π l' → l ∈ antecedents \/ l ∈ gs) ⌝.
Proof.
  (* By induction on the set [locs]. *)
  pattern locs. eapply set_ind_L; clear locs.
  (* Case: ∅. *)
  { intros. rewrite gmap_mdelete_empty.
    iIntros "[Hauth _]". iFrame "Hauth".
    iPureIntro. exists ∅. split; try set_solver. intros ?. set_solver. }
  (* Case: {[l]} ∪ locs. *)
  { intros l locs ? IH σ π ?.
    rewrite -> big_sepS_union by set_solver.
    rewrite big_sepS_singleton.
    rewrite -> gmap_mdelete_cons' by set_solver.
    iIntros "(Hauth & Hl & Hlocs)".
    rewrite /mapsfrom_set.
    iDestruct "Hl" as (ps) "[Hl %Hps]".
    iMod (pred_free_singleton with "Hauth Hl") as "[Hauth %Hl]"; first easy.
    iMod (IH with "[$]") as "[Hauth %Hlocs]".
    { rewrite dom_delete_L. set_solver. }
    iFrame "Hauth". iPureIntro.
    destruct Hl as (ls', (Hincl&Hls')).
    destruct Hlocs as (ls'', (Hls''&?)).
    exists (ls' ⊎ ls'').
    split.
    { intros ?. rewrite gmultiset_elem_of_disj_union. intros [].
      { now apply Hls'. }
      { now apply Hls''. } }
    intros m m'. rewrite elem_of_union elem_of_singleton.
    destruct 1.
    + subst. intros Hm.
      eapply gmultiset_elem_of_subseteq in Hm.
      2:apply Hincl.
      apply gmultiset_elem_of_disj_union in Hm. destruct Hm as [Hm|Hm].
      { left. apply Hps, dom_to_gmultiset, gmultiset_elem_of_dom. easy. }
      { right. multiset_solver. }
    + rewrite <- (predecessors_delete_ne _ l) by set_solver.
      multiset_solver. }
Qed.

(* If the predecessor set of [l'] is [gs1] and if we hold a share
   [ls1] of it, then we can update this to [gs2] and [ls2], provided
   [gs1 ⊎ ls2 = gs2 ⊎ ls1] holds. This expresses the fact that the
   share that we do not hold remains unchanged. *)

(* [gs2] is determined: it is [(gs1 ⊎ ls2) ∖ ls1]. *)

Lemma pred_update σ π l' q gs1 gs2 ls1 ls2 :
  π !! l' = Some gs1 →
  dom π ⊆ dom σ ->
  (q=0%Qz -> AllNeg ls2) ->
  (of_gmultiset gs1) ⊎ ls2 ≡ (of_gmultiset gs2) ⊎ ls1 →
  pred σ π -∗ mapsfrom l' q ls1 ==∗
  pred σ (<[ l' := gs2 ]> π) ∗ mapsfrom l' q ls2.
Proof.
  iIntros (Hπl' ? Hls2 ?) "[%μ [%Hμ Hauth]] [%J Hfrag]".

  assert (l' ∈ dom π).
  { now apply elem_of_dom. }

  assert (exists ns, μ !! l' = Some ns) as (ns,Hns).
  { destruct Hμ as [Hd]. apply elem_of_dom. rewrite Hd. set_solver. }

  iAssert (|==> own γ (● ((full_gmultiset <$> <[l':=gs2]> π) ⋅ μ)) ∗ own γ (◯ {[l' := {| frac := q; supp := ls2; neglz := Hls2 |}]}))%I with "[Hauth Hfrag]" as ">[Hauth Hfrag]".
  { rewrite -own_op.
    iApply (own_update_2 with "[Hauth //] [$]").
    eapply auth_update.
    rewrite fmap_insert.

    setoid_rewrite <- (insert_id _ _ _ Hns) at 2.
    setoid_rewrite gmap_op at 2.
    erewrite <- (insert_merge _ _ _ l').
    2:{ rewrite -Some_op. easy. }
    eapply singleton_local_update.
    { rewrite lookup_merge lookup_fmap Hπl' Hns. simpl. rewrite -Some_op //. }
    { apply local_update_unital_discrete.
      intros z Hv Hz.
      split; try easy.
      inversion_clear Hz as [? ?]. constructor; try easy. simpl in *.
      smultiset_solver. } }
  iSplitL "Hauth"; iExists _; eauto using tied_update.
Qed.

(* We can always allocate an empty fracset. *)
Lemma fracset_local_alloc_unit l μ :
  l ∈ dom μ ->
  (μ, ε) ~l~> (μ, {[l := ε]}).
Proof.
  intros ?.
  apply local_update_unital_discrete.
  intros z Hv Hz.
  split; try easy.
  intros x. rewrite left_id in Hz.
  specialize (Hz x).
  rewrite Hz lookup_op.
  destruct (decide (x=l)); subst.
  { rewrite lookup_singleton.
    destruct (z !! l) eqn:E; rewrite E.
    { by rewrite -Some_op left_id. }
    { exfalso.
      rewrite E in Hz. inversion Hz as [|Hz'].
      symmetry in Hz'.
      by apply not_elem_of_dom in Hz'. } }
  { by rewrite lookup_singleton_ne // left_id. }
Qed.

(* We can get an empty mapsfrom from every allocated location. *)
Lemma get_empty_mapsfrom l' σ π :
  l' ∈ dom σ ->
  pred σ π ==∗
  pred σ π ∗ mapsfrom l' 0%Qz ∅.
Proof.
  iIntros (?) "[%μ [%Hμ Hauth]]".
  iMod (own_update with "[$]") as "Hauth".
  { eapply auth_update_alloc.
    apply fracset_local_alloc_unit with (l:=l').
    destruct Hμ as [Hd ? ?].
    rewrite dom_union_with dom_fmap_L Hd.
    set_solver. }
  rewrite own_op. iDestruct "Hauth" as "[Hauth ?]".
  iSplitL "Hauth"; iExists _; eauto.
Qed.

Lemma pred_update_no_mapsfrom σ π l' (ps1 ps2 : gmultiset L) (ls2 : smultiset L):
  π !! l' = Some ps1 →
  dom π ⊆ dom σ ->
  (of_gmultiset ps1) ⊎ ls2 ≡ (of_gmultiset ps2) →
  AllNeg ls2 ->
  pred σ π ==∗
  pred σ (<[ l' := ps2 ]> π) ∗ l' ↤{0} ls2.
Proof.
  iIntros (Hπl' ? Hls2 ?) "Hpred".
  iMod (get_empty_mapsfrom l' with "[$]") as "[? ?]".
  { assert (l' ∈ dom π) by now apply elem_of_dom. set_solver. }
  iMod (pred_update with "[$] [$]"); eauto.
  by rewrite right_id.
Qed.

Lemma pred_update_freed σ π l' ms :
  l' ∈ dom σ ->
  (∀m, m ∈ ms → freed σ m) →
  pred σ π ==∗
  pred σ π ∗ l' ↤{0} (of_gmultiset_neg ms).
Proof.
  iIntros (Hl' ?) "Hpred".
  iMod (get_empty_mapsfrom with "[$]") as "[Hauth Hmapsfrom]".
  { apply Hl'. }
  iDestruct "Hauth" as "[%μ [%Hμ Hauth]]".

  generalize Hμ. intros [Hdμ Hneg Hco].

  assert (exists ns, μ !! l' = Some ns) as (ns,Hns).
  { apply elem_of_dom. now rewrite Hdμ. }

  assert (AllNeg (of_gmultiset_neg ms)) as Halln.
  { smultiset_solver. }
  assert (AllNeg (of_gmultiset_neg ms ⊎ supp ns)) as Halln'.
  { specialize (Hneg _ _ Hns).
    assert (AllNeg (supp ns)) by (now apply neglz).
    smultiset_solver. }

  iAssert (|==> own γ (● ((full_gmultiset <$> π) ⋅ (<[l':=mk_nf 0%Qz (of_gmultiset_neg ms ⊎ supp ns) (fun _ => Halln')]>)μ)) ∗ own γ (◯ {[l' := {| frac := 0%Qz; supp := of_gmultiset_neg ms; neglz := fun _ => Halln |}]}))%I with "[Hauth Hmapsfrom]" as ">[Hauth ?]".
  { rewrite -own_op.
    iDestruct "Hmapsfrom" as "[%X ?]".
    iApply (own_update_2 with "[Hauth] [$]"); last iFrame.
    apply auth_update.

    setoid_rewrite gmap_op at 2.

    destruct (π !! l') eqn:E.
    { setoid_rewrite <- (insert_id _ _ _ E) at 2.
      rewrite fmap_insert.
      erewrite <- (insert_merge op (full_gmultiset <$> π) μ l').
      2:{ rewrite -Some_op //. }
      eapply singleton_local_update.
      { rewrite lookup_merge lookup_fmap E Hns. simpl. rewrite -Some_op //. }

      apply local_update_unital_discrete.
      intros z _ Hz.
      split; try easy.
      constructor.
      { specialize (Hneg _ _ Hns).
        apply nfrac_equiv_frac in Hz. simpl in *.
        rewrite Hneg in Hz. easy. }
      { apply nfrac_equiv_supp in Hz. simpl in *.
        smultiset_solver. } }

    (* Not in π. Why not. *)
    { erewrite <- (insert_merge_r op _ μ l').
      2:{ rewrite lookup_fmap E. simpl. rewrite left_id //. }
      eapply singleton_local_update.
      { rewrite lookup_merge lookup_fmap E Hns. simpl. rewrite left_id //. }

      (* LATER facto *)
      apply local_update_unital_discrete.
      intros z _ Hz.
      split; try easy.
      constructor.
      { specialize (Hneg _ _ Hns).
        apply nfrac_equiv_frac in Hz. simpl in *.
        rewrite Hneg in Hz. easy. }
      { apply nfrac_equiv_supp in Hz. simpl in *.
        smultiset_solver. } } }

  iSplitL "Hauth"; iExists _; iFrame; eauto.
  iPureIntro.
  eapply tied_update_freed; eauto. intros ? Hi.
  apply smultiset_elem_of_disj_union in Hi.
  destruct Hi; eauto. smultiset_solver.
Qed.

(* When confronted with the authoritative assertion [pred dσ π], the assertion
   [l' ↤{q} ls] allows registering [l] as a new predecessor of [l']. The
   authoritative predecessor map is updated from [π] to [register l l' π],
   while the mapsfrom assertion becomes [l' ↤{q} (ls ⊎ {[l]})]. It is worth
   noting that the fraction [q] is not required to be 1. *)

Lemma pred_register σ π l l' q ls :
  dom π ⊆ dom σ ->
  q <> 0%Qz ->
  pred σ π -∗ l' ↤{q} ls ==∗
  pred σ (register l l' π) ∗ l' ↤{q} (ls ⊎ {[+l+]}).
Proof.
  iIntros (? ?) "Hauth Hmapsfrom".
  iDestruct (exploit_mapsfrom with "Hauth Hmapsfrom")
    as %(ps & Hπl' & _).
  1,2:easy.
  rewrite /register.
  erewrite lookup_total_correct by eauto.
  iMod (pred_update σ π l' q ps (ps ⊎ {[+ l +]}) ls (ls ⊎ {[+ l +]}) Hπl'
         with "Hauth Hmapsfrom") as "[? ?]"; try easy.
  { rewrite of_gmultiset_disj_union of_gmultiset_singleton. smultiset_solver. }
  by iFrame.
Qed.

(* The reverse of the previous lemma. Because this is a decreasing update,
   the storement is more complex, and the final store [π'] is not known
   exactly; we get a lower bound and an upper bound on it. *)

Lemma pred_unregister σ π l l' :
  dom π ⊆ dom σ ->
  l ∈ predecessors π l' ->
  pred σ π ==∗
  ∃π',
  pred σ π' ∗ l' ↤{0} {[-l-]} ∗ ⌜ unregister l l' π ≾ π' ∧ π' ≾ π ⌝.
Proof.
  iIntros (? Hl') "Hauth".

  assert (exists gs, π !! l' = Some gs /\ l ∈ gs) as (gs,(?&?)).
  { rewrite /predecessors in Hl'. destruct (π !! l'); set_solver. }

  rewrite /unregister.
  erewrite lookup_total_correct; last eauto.
  iMod (pred_update_no_mapsfrom σ π l' gs (gs ∖ {[l]}) with "[$]") as "[Hauth Hfrag]"; eauto.
  { assert ({[+ l +]} ⊆ gs ) by multiset_solver.
    rewrite of_gmultiset_difference //. }
  { apply AllNeg_of_gmultiset_neg. }
   rewrite of_gmultiset_neg_singleton.
  iModIntro. iExists _. iFrame.
  iPureIntro.
  split; eauto with approx.
Qed.

(* We now wish to iterate the above lemma so as to register an address [l] as
   a new predecessor of [l'], for every address [l'] in a certain list.

   For each address [l'] in the list, we must require [l' ↤{q} ls], for a
   certain fraction [q] and a certain list [ls] of pre-existing predecessors.

   This leads us to parameterizing the lemma with a list of triples, where
   each triple is of the form [(l', q, ls)], and is interpreted as a
   description of the assertion [l' ↤{q} ls].

   The fact that we allow fractional ownership seems crucial here. Indeed,
   because a newly-allocated block may have two fields that contain the same
   pointer, we must allow two triples in this list to concern the same address
   [l']. If we required full ownership of every triple in the list, then the
   iterated conjunction of these triples would be unsatisfiable. *)

(* That said, considering our current needs, working with lists of triples of
   arbitrary length is slightly overkill. The lemma [ph_alloc] is applied to a
   list of length 0, because we initialize every memory block with unit
   values. The lemma [ph_update] is applied to lists of length at most 1,
   because our store instruction updates only one field at a time, so destroys
   at most one edge and creates at most one edge. *)

Implicit Types triple :      (L * Qz * smultiset L).

Implicit Type triples : list (L * Qz * smultiset L).

(* interpret1 & interpret are used for points to of the new value.
   As we will register a new predecessor, they cannot be empty. *)
Definition interpret1 triple : iProp Σ :=
  let '(l', q, ls) := triple in ⌜q<>0%Qz⌝ ∗ l' ↤{q} ls.

Definition interpret triples : iProp Σ :=
  [∗ list] triple ∈ triples, interpret1 triple.

Definition interpret_unregister1 l l' : iProp Σ :=
  l' ↤{0%Qz} {[- l -]}.

Definition interpret_unregister l xs : iProp Σ :=
  [∗ list] l' ∈ xs, interpret_unregister1 l l'.

Definition address triple :=
  let '(l', q, ls) := triple in l'.

Definition addresses triples : gmultiset L :=
  list_to_set_disj (map address triples).

Definition update l triple :=
  let '(l', q, ls) := triple in (l', q, ls ⊎ {[+l+]}).

Lemma interpret_nil :
  interpret [] = True%I.
Proof. reflexivity. Qed.

Lemma interpret_unregister_nil l :
  interpret_unregister l [] = True%I.
Proof. reflexivity. Qed.

Lemma interpret_unregister_cons l x xs :
  interpret_unregister l (x::xs) = (interpret_unregister1 l x ∗ interpret_unregister l xs)%I.
Proof. by rewrite /interpret_unregister big_opL_cons. Qed.

Lemma interpret_singleton l' q ls :
  q <> 0%Qz ->
  interpret [(l', q, ls)] ≡ (l' ↤{q} ls)%I.
Proof.
  intros.
  rewrite /interpret. simpl. iSplit; eauto.
  iIntros "([? ?] & _)". iFrame.
Qed.

Lemma addresses_cons triple triples :
  addresses (triple :: triples) =
  addresses triples ⊎ {[+ address triple +]}.
Proof.
  unfold addresses. simpl. multiset_solver.
Qed.

Lemma exploit_triples_dom σ π triples :
  dom π ⊆ dom σ ->
  pred σ π -∗
  interpret triples -∗
  ⌜ ∀ l', l' ∈ addresses triples → l' ∈ dom π ⌝.
Proof.
  intros.
  induction triples as [| [[l' q] ls] triples ]; simpl;
  iIntros "Hauth Htriples".
  { iPureIntro. multiset_solver. }
  iDestruct "Htriples" as "[[%Hq Htriple] Htriples]". simpl.
  iDestruct (exploit_mapsfrom_dom with "Hauth Htriple") as %Hhead.
  1,2:easy.
  iDestruct (IHtriples with "Hauth Htriples") as %Htail.
  iPureIntro.
  intro. rewrite addresses_cons. multiset_solver.
Qed.

Lemma dom_fold_register dσ π (addrs : gmultiset L) l :
  dom π ⊆ dσ ->
  (∀ l' : L, l' ∈ addrs → l' ∈ dom π) ->
  dom (set_fold (register l) π addrs) ⊆ dσ.
Proof.
  induction addrs as [| x addrs] using gmultiset_ind;
    intros Hd Ha.
  { multiset_solver. }
  { rewrite gmultiset_disj_union_comm.
    rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton.
    multiset_solver. }
Qed.

Lemma pred_foldr_register l :
  ∀ triples σ π,
  dom π ⊆ dom σ ->
  pred σ π -∗ interpret triples ==∗
  pred σ (set_fold (register l) π (addresses triples)) ∗
  interpret (map (update l) triples).
Proof.
  induction triples as [| [[l' q] ls] triples ];
  simpl; intros; subst; simpl; [eauto|].
  iIntros "? [Hi ?]".
  iDestruct (exploit_triples_dom with "[$] [$]") as "%Hi". easy.
  iMod (IHtriples with "[$] [$]") as "[? ?]". easy.
  iDestruct "Hi" as "[%Hq ?]".
  iMod (pred_register with "[$] [$]") as "[? ?]".
  { eauto using dom_fold_register. }
  { easy. }
  rewrite addresses_cons.
  rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton.
  by iFrame.
Qed.

Lemma pred_foldr_unregister l :
  ∀ σ (xs : list L) π,
    dom π ⊆ dom σ ->
   (forall l', gmultiset.multiplicity l' (list_to_set_disj xs) <= gmultiset.multiplicity l (predecessors π l')) ->
  pred σ π  ==∗
  ∃ π',
  pred σ π' ∗
  interpret_unregister l xs ∗
  ⌜ foldr (unregister l) π xs ≾ π' ∧ π' ≾ π ⌝.
Proof.
  induction xs as [| x xs];
    simpl; intros ? ? Hxs; subst; simpl.
  { iIntros. iModIntro. iExists _. iFrame. rewrite interpret_unregister_nil. eauto. }
  iIntros "Hauth".
  rewrite interpret_unregister_cons.
  iMod (IHxs with "Hauth")
    as (π1) "(Hauth & Htriples & %Hlo1 & %Hhi1)".
  { easy. }
  { intros l'. specialize (Hxs l').
    rewrite gmultiset.multiplicity_disj_union in Hxs.
    destruct (decide (x=l')); subst.
    { rewrite gmultiset.multiplicity_singleton in Hxs. lia. }
    { rewrite gmultiset.multiplicity_singleton_ne // in Hxs. } }
  iMod (pred_unregister with "Hauth")
    as (π2) "(Hauth & Htriple & %Hlo2 & %Hhi2)"; last iFrame.
  { destruct Hhi1 as (->&?). easy. }
  { destruct Hlo1 as (?&Hlo1). specialize (Hlo1 x l).
    assert (l∈ predecessors (foldr (unregister l) π xs) x); last multiset_solver.
    rewrite /elem_of /gmultiset_elem_of.
    rewrite predecessors_foldr_unregister.
    rewrite decide_True //.
    specialize (Hxs x).
    rewrite gmultiset.multiplicity_disj_union gmultiset.multiplicity_singleton in Hxs. lia. }
  iModIntro. iExists _. iFrame. iPureIntro.
  eauto using approx_transitive, unregister_approx.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma invariant_alloc_no_pointers σ π l b :
  invariant σ π →
  l ∉ dom σ →
  b ≠ deallocated →
  pointers b = ∅ →
  invariant (<[l:= b]> σ) (<[l:=∅]> π).
Proof.
  intros ? ? ? Hb.
  assert (<[l:=∅]> π = set_fold (register l) (<[l:=∅]> π) (pointers b)) as ->.
  { by rewrite Hb. }
  eapply invariant_alloc; try easy.
  rewrite Hb. set_solver.
Qed.

(* Our store interpretation predicate is preserved by the allocation of a
   new block [b] at a fresh location [l].

   As explained earlier, the user must provide a list of triples
   [(l', q, ls)], where [l'] ranges over the locations contained
   in the block [b], and must provide the assertion [l' ↤{q} ls]
   that corresponds to each of these triples.

   After the operation, the location [l] is added as an extra predecessor
   in each of these triples: each such triple becomes [l' ↤{q} ls ⊎ {[l]}].

   In addition, the user receives [l ↦ b], as in ordinary Separation Logic,
   and [l ↤ ∅], which stores that the new block has no predecessors. *)

Lemma ph_alloc σ l b :
  σ !! l = None →
  b ≠ deallocated →
  pointers b = ∅ →
  ph_interp σ ==∗
  ph_interp (<[l:=b]> σ) ∗
  l ↦ b ∗ l ↤ ∅ ∗ meta_token l ⊤.
Proof.
  intros Hσl ? Hpointers.
  rewrite /ph_interp.
  iIntros "[Hh Hph]".
  iDestruct "Hph" as (π) "(Hauth & %Hinv)".
  generalize Hinv; intros (Hco & Hmirror & Hclosure).

  (* [l] is fresh, so is not in the domain of [σ]. *)
  assert (l ∉ dom σ) by eauto.
  (* By coincidence, the domain of [π] is a subset of that of [σ],
     so [l] is not the domain of [π] either. *)
  assert (Hπl: l ∉ dom π) by eauto using use_coincidence_reverse.

  (* We are now ready to update the ghost store, in two steps: *)

  (* Step 1. Extend the heap resource with a mapping of [l] to [b]. *)
  iMod (gen_heap_alloc σ l b Hσl with "Hh") as "(Hh & Hlb & ?)".

  (* Step 2. Move from [π] to [π'], which extends [pi] with a mapping of [l]
     to an empty multiset of predececessors. At the same time, we obtain the
     assertion [l ↤ ∅]. *)
  set (π' := <[l:=∅]> π).
  iMod (pred_alloc _ π l with "Hauth") as "[Hauth Hmapsfrom]".
  1-3: eauto using invariant_dom.

  (* Conclude. *)

  iModIntro. iFrame. iExists _. iFrame.
  iPureIntro.
  eauto using invariant_alloc_no_pointers.
Qed.

(* ------------------------------------------------------------------------ *)

(* An ad hoc version of the lemma [gen_heap_valid_big] in iris.v. *)

Local Lemma gen_heap_valid_big σ locs :
  gen_heap_interp σ ∗
  ([∗ set] l ∈ locs, ∃ b, l ↦ b) -∗
  ⌜ locs ⊆ dom σ ⌝.
Proof.
  (* By induction on the set [locs]. *)
  pattern locs. eapply set_ind_L; clear locs.
  (* Case: ∅. *)
  { eauto. }
  (* Case: {[l]} ∪ locs. *)
  { intros l locs Hl IH.
    rewrite -> !big_sepS_union, !big_sepS_singleton by set_solver.
    iIntros "(Hh & Hl & Hlocs)".
    iDestruct "Hl" as (b) "Hl".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hone.
    assert (l ∈ dom σ) by eauto.
    iDestruct (IH with "[$]") as %Htwo.
    iPureIntro. set_solver. }
Qed.

(* ------------------------------------------------------------------------ *)

(* The predicate [ph_interp σ] allows deallocating a set of locations [locs],
   provided this set is closed under predecessors. *)

(* This operation consumes [∃ b, l ↦ b] and [mapsfrom_set l 1%Qp locs]
   for every location [l] in the set [locs]. It does not require any
   information about the successors of the block [b], and does not update
   their predecessor fields. We adopt a mechanism that allows delayed
   updates: we produce a proof that the location [l] has been deallocated.
   A separate rule allows removing a dead location from a predecessor set. *)

(* We produce a witness that the set [locs] contains no roots and is closed
   under predecessors. This fact is stored in terms of successors. *)

Lemma pred_update_store_deallocate σ π locs :
  pred σ π -∗ pred (deallocate locs σ) π.
Proof.
  iIntros "[%μ [%Hμ Hauth]]".
  iExists _. eauto using tied_store_deallocate.
Qed.

Lemma ph_free_group σ locs :
  ph_interp σ ∗
  ([∗ set] l ∈ locs, ∃b, l ↦ b ) ∗
  ([∗ set] l ∈ locs, mapsfrom_set l locs)
  ==∗
  ph_interp (deallocate locs σ) ∗
  ††locs ∗
  ⌜ ∀ m m', m' ∈ successors σ m → m' ∈ locs → m ∈ locs ⌝.
Proof.
  rewrite /ph_interp.
  iIntros "((Hh & Hph) & Hmapsto & Hmapsfrom)".
  iDestruct "Hph" as (π) "(Hauth & %Hinv)".

  (* [locs] is a subset of the domain of [σ], and does not contain any root. *)
  iDestruct (gen_heap_valid_big with "[$]") as "%Hnroot".

  (* Update [σ] by deallocating every location in the set [locs]. *)
  iMod (iris.gen_heap_update_big locs with "[$]") as "(Hh & Hmapsto)".

  (* For every [l] in [locs], we have full ownership of [l ↦ deallocated].
     Discard a fraction of this fact, so as to make it persistent.
     Deallocation is forever. *)
  iMod (iris.mapsto_persist_big with "[$]") as "Hmapsto".

  (* Update [π] by removing [locs] from its domain. *)
  iMod (pred_free_group with "[$]") as "[Hauth %Hclosed]".
  { eauto using invariant_dom. }

  destruct Hclosed as (ls',(Hfreed & Hclosed)).

  (* The invariant is preserved. Conclude. *)
  iModIntro. iFrame "Hh Hmapsto".
  iSplitL "Hauth".
  + iExists _. iDestruct (pred_update_store_deallocate with "[$]") as "?". iFrame.
    iPureIntro.
    eapply invariant_free; eauto.
  + eauto using successors_predecessors_corollary.
Qed.

(* Deallocating a single location is a special case. *)

(* The memory block at address [l] may contain one or more pointers
   to itself. *)

(* The lemma is stored in terms of [mapsfrom], as opposed to
   [mapsfrom_set], because this may be more convenient. We may
   end up needing both versions anyway. *)

Lemma ph_free_singleton σ l b ls :
  dom ls ⊆ {[l]} →
  ph_interp σ             ∗ l ↦ b ∗ l ↤ ls ==∗
  ph_interp (<[l:=deallocated]> σ) ∗ †l ∗
  ⌜ ∀ m, l ∈ successors σ m → m = l ⌝.
Proof.
  iIntros (Hls) "(Hph & Hmapsto & Hmapsfrom)".
  iDestruct (exploit_mapsto with "[$] [$]") as %Hdom.
  iMod (ph_free_group σ {[l]} with "[Hph Hmapsto Hmapsfrom]")
    as "(Hph & Hddag & %Hfacts)".
  { iFrame "Hph".
    rewrite !big_sepS_singleton. iSplitL "Hmapsto".
    + eauto.
    + unfold mapsfrom_set. iExists ls. iFrame "Hmapsfrom".
      easy. }
  rewrite /deallocate. rewrite -> gmap_mset_singleton by eauto.
  rewrite -> (ddag_singleton l).
  iFrame "Hph Hddag". iPureIntro.
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)

(* The "cleanup" reasoning rule stores that a deallocated location [m] can
   be removed from a predecessor set. *)

(* This rule can be stored in several different ways; e.g., one may first
   propose a storement that focuses on one location [m] and later generalize
   to a set or multiset of locations, or adopt the converse approach; and if
   one chooses to focus on one location, one may remove just one copy of
   this location from the predecessor multiset, or one may remove all copies
   of it at once. We choose one path. *)


Lemma ph_cleanup σ l' ms :
  l' ∈ dom σ ->
  (∀m, m ∈ ms → freed σ m) →
  ph_interp σ  ==∗
  ph_interp σ ∗ l' ↤{0} (of_gmultiset_neg ms).
Proof.
  intros Hl' Hms.
  rewrite /ph_interp.
  iIntros "(Hh & [%π [Hπ %Hinv]])".

  iMod (pred_update_freed σ π l' _ Hl' Hms with "Hπ") as "[? ?]".
  iFrame.
  iExists _. by iFrame.
Qed.

Lemma ph_cleanup_singleton σ l' m :
  l' ∈ dom σ ->
  ph_interp σ ∗ †m ==∗
  ph_interp σ ∗ l' ↤{0} {[-m-]}.
Proof.
  iIntros (?) "(Hh & Hmapsto)".
  iDestruct (exploit_discarded σ m with "Hh Hmapsto") as %?.
  iMod (ph_cleanup σ l' {[+ m +]} with "[$]").
  { easy. }
  { intros m'. rewrite gmultiset_elem_of_singleton. intros ->. eauto. }
  rewrite of_gmultiset_neg_singleton.
  by iFrame.
Qed.

(*
(* TODO may need to be reformulated in a more convenient way;
   see also wp_cleanup.v *)
Lemma ph_cleanup_group σ l' q ls ms :
  ph_interp σ ∗ l' ↤{q} ls ∗ ††(dom ms) ==∗
  ph_interp σ ∗ l' ↤{q} (ls ∖ ms).
Proof.
  iIntros "(Hh & Hmapsfrom & Hmapsto)".
  iDestruct (exploit_discarded_group σ (dom ms) with "Hh Hmapsto") as %Hdms.
  assert (Hms: ∀ l, l ∈ ms → freed σ l).
  { intro. rewrite <- gmultiset_elem_of_dom. eauto. }
  iMod (ph_cleanup σ l' q ls ms Hms with "[$]").
  by iFrame.
Qed.
 *)

Lemma pred_update_store σ π l b b':
  b ≠ deallocated →
  b' ≠ deallocated →
  pred (<[l := b]> σ) π -∗ pred (<[l := b']> σ) π.
Proof.
  iIntros (? ?) "[%μ [%Hμ ?]]".
  iExists _. eauto using tied_update_store.
Qed.

Lemma ph_update σ l b b' new_triples :
  b ≠ deallocated →
  b' ≠ deallocated →
  addresses new_triples = new_pointers b b' →
  ph_interp (<[l := b]> σ) ∗
  interpret new_triples ∗
  l ↦ b ==∗
  ph_interp (<[l := b']> σ) ∗
  interpret_unregister l (elements (old_pointers b b')) ∗
  interpret (map (update l) new_triples) ∗
  l ↦ b'.
Proof.
  intros Hb Hoaddr Hnaddr.
  rewrite /ph_interp.
  iIntros "((Hh & Hph) & Hntriples & Hmapsto)".
  iDestruct "Hph" as (π) "(Hauth & %Hinv)".

  assert (dom π ⊆ dom (<[l:=b]> σ)) by (eauto using invariant_dom).

  iDestruct (exploit_triples_dom with "Hauth Hntriples") as %Hlive; try easy.
  rewrite Hnaddr in Hlive.

  (* Update [σ] with a mapping of [l] to [b']. *)
  iMod (gen_heap_update _ l _ b' with "Hh Hmapsto") as "(Hh & Hmapsto)".
  rewrite insert_insert. iFrame.

  (* Update [π] by unregistering every edge from [l] to a location [l']
     in [block_pointers b ∖ block_pointers b'] and by registering every
     edge from [l] to some [l'] in [block_pointers b' ∖ block_pointers b]. *)

  iMod (pred_foldr_unregister with "Hauth")
    as (π') "(Hauth & Hotriples & %Hlo & %Hhi)"; last iFrame.
  { easy. }
  { rewrite /old_pointers.
    intros l'. destruct Hinv as (? & Hmir & ?).
    specialize (Hmir l l').
    rewrite successors_insert in Hmir.
    rewrite list_to_set_disj_elements.
    multiset. lia. }

  iMod (pred_foldr_register l new_triples with "Hauth Hntriples")
    as "(Hauth & Hntriples)".
  { destruct Hhi as (->&_). easy. }


  (* Conclude. *)
  iModIntro. iFrame. iExists _.
  iDestruct (pred_update_store with "[$]") as "?"; last iFrame; eauto.
  iPureIntro.
  (* The invariant is preserved. *)
  rewrite Hnaddr.
  eapply (invariant_update_imprecise σ l b b' π π' Hinv);
    eauto using gmultiset_in_set_in_elements.
Qed.

(* ------------------------------------------------------------------------ *)

(* Timelessness. *)

Global Instance timeless_mapsfrom l q ls :
  Timeless (mapsfrom l q ls).
Proof. apply _. Qed.

Global Instance timeless_mapsfrom_set l locs :
  Timeless (mapsfrom_set l locs).
Proof. apply _. Qed.

Global Instance timeless_dag l :
  Timeless (†l).
Proof. apply _. Qed.

Global Instance timeless_ddag locs :
  Timeless (††locs).
Proof. apply _. Qed.

(* ------------------------------------------------------------------------ *)

End ReasoningRules.

(* ------------------------------------------------------------------------ *)

(* Notations for assertions. *)

(* Fractional ownership of a memory block, where [q] is a fraction. *)

Notation "l ↦{ q } b" := (mapsto l (DfracOwn q)%Qp b)
  (at level 20, q at level 50, format "l  ↦{ q }  b") : bi_scope.

(* Full ownership of a memory block. *)

Notation "l ↦ b" := (l ↦{ 1%Qp } b)%I
  (at level 20) : bi_scope.

(* Fractional ownership of a predecessor set, where [q] is a fraction. *)

Notation "l ↤{ q } ls" :=
  (mapsfrom l q%Qz ls)
  (at level 20, format "l  ↤{ q }  ls")
: bi_scope.

(* Full ownership of a predecessor set. *)

Notation "l ↤ ls" :=
  (l ↤{ 1%Qz } ls)%I
  (at level 20, format "l  ↤  ls")
: bi_scope.

(* Persistent knowledge that a location has been deallocated. *)

Notation "† l" := (gen_heap.mapsto l DfracDiscarded deallocated)%I
  (at level 20) : bi_scope.

(* Persistent knowledge that a group of locations have been deallocated. *)

Notation "†† ls" := ([∗ set] l ∈ ls, †l)%I
  (at level 20) : bi_scope.

(* ------------------------------------------------------------------------ *)

(* The following definitions have to do with initializing the heap.
   They are used in the proof of adequacy. *)

Module Initialization.

  Definition phΣ L B `{Countable L} : gFunctors := #[
    gen_heapΣ L B;
    GFunctor (predR L)
  ].

  Class phPreG L B Σ `{Countable L} := {
    phPreG_heap :> gen_heapGpreS L B Σ;
    phPreG_pred :> inG Σ (predR L);
  }.

  Global Instance subG_phPreG {L B Σ} `{Countable L} :
    subG (phΣ L B) Σ → phPreG L B Σ.
  Proof. solve_inG. Qed.

  Lemma ph_init `{Hypotheses L B, !phPreG L B Σ} :
    ⊢ |==> ∃ _ : phG L B Σ,
    ph_interp ∅.
  Proof.
    iIntros. rewrite /ph_interp.
    (* Allocate the ghost heap component. *)
    iMod (gen_heap_init ∅) as (ghG) "(Hh & _ & _)".
    (* Allocate the ghost cell that holds [π]. *)
    set (π := ∅ : gmap L (gmultiset L)).
    set (μ := ∅ : gmap L (fracset L)).

    iMod (own_alloc (● (fmap full_gmultiset π ⋅ μ) : predR L)) as (γ) "Hpred".
    { rewrite auth_auth_valid. done. }
    (* Conclude. *)
    iExists (PhG L B Σ _ _ ghG _ γ).
    iModIntro.
    iFrame. (* this cancels out "Hh" *)
    iExists π.
    iSplitL; eauto using invariant_init.
    iExists _. eauto using tied_init.
  Qed.

End Initialization.
