From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.fracz Require Import qz qz_cmra smultiset.
From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language.

From spacelambda Require Export wp ph.

Global Notation dom := (dom (gset loc)).

Set Implicit Arguments.

Class interpGS (Σ : gFunctors) :=
  InterpG { iinvgs :> invGS Σ;
    iphg :> phG loc store.block Σ; (* For the store *)
    idiamonds :> inG Σ (authR ugfracUR); (* A camera for diamonds *)
    ictx :> inG Σ (authUR (gmapUR loc fracR)); (* A camera for context *)
    γctx : gname; (* A name for the ghost cell of the context *)
    γdia : gname; (* A name for the ghost cell of the diamonds *)
    }.

Ltac destruct_interp H :=
  iDestruct H as "[%θ [%Hσ [%Hθ [%Hθvalid [%Hσθ [Hph [Hk [Hctx Hdiams]]]]]]]]".

Section Interp.

Context `{iG:!interpGS Σ}.

Definition interp (b:bool) (maxsize:nat) (k:lctx) (σ:store) (ls:gset loc) : iProp Σ :=
    (* Whereas [σ] represents the physical machine store,
       [θ] is the conceptual machine store. *)
    ∃θ,

    ⌜correct (dom k ∪ ls) σ⌝ ∗
    ⌜correct (dom k ∪ ls) θ⌝ ∗
    ⌜valid_store maxsize θ⌝ ∗
    ⌜related (dom k ∪ ls) σ θ⌝ ∗

    (* The conceptual store is synchronized with our [mapsto] and [mapsfrom]
       assertions. *)
    ph_interp θ ∗

    (* Assert fraction 1 for every location in the store *)
    own γctx (● (gset_to_gmap 1%Qp (dom σ))) ∗

    (* Store in the invariant the frag auth of locations in the context
       Therefore, if someone shows us [own γctx (◯ (1,l))] we know that l is not in k *)
    (if b then own γctx (◯ k) else True ) ∗

    (* The number of space credits currently in circulation is (at most)
       [available θ], the available space in the conceptual machine store. *)
    own γdia (@auth_auth ugfracUR (DfracOwn 1) (nat_to_Qz (available maxsize θ))) .

(* ------------------------------------------------------------------------ *)

Definition Stackable (l:loc) q :=
  own γctx (◯ ({[l:=q]})).

Lemma exploit_Stackable_full maxsize k (σ:store) ls l :
  interp true maxsize k σ ls -∗ Stackable l 1%Qp -∗ ⌜l ∉ (dom k) ⌝.
Proof.
  iIntros "Hi Hn".
  destruct_interp "Hi".
  iDestruct (own_valid_2 with "Hctx Hn") as "%Hn".
  iPureIntro.
  apply stdpp.prove_not_in_dom.
  rewrite -auth_frag_op  in Hn.
  rewrite auth_frag_valid in Hn.
  specialize (Hn l).
  rewrite lookup_op in Hn.
  rewrite lookup_singleton in Hn.
  apply exclusive_Some_r in Hn.
  2:apply _.
  easy.
Qed.

Lemma Stackable_join (l:loc) q1 q2 :
  Stackable l q1 -∗ Stackable l q2 -∗ Stackable l (q1+q2)%Qp.
Proof. iIntros. iApply from_sep. iFrame. Qed.

(* ------------------------------------------------------------------------ *)
(* We are going to store [interp_shift]. It is more convenient to speak
   about sets, than iteration on sets. We therefore introduce "already iterated"
   versions of [Stackable]. *)

Definition Stackables k : iProp Σ :=
  own γctx (◯ k).

Lemma Stackables_empty :
  ⊢ |==> Stackables ∅.
Proof.
  iStartProof.
  unfold Stackables. iMod (own_unit (authUR (gmapUR loc frac.fracR)) γctx).
  iMod (own_update with "[$]"); last by iFrame.
  easy.
Qed.

Lemma Stackables_union k1 k2 :
  Stackables k1 ∗ Stackables k2 ⊢ Stackables (k1 ⋅ k2).
Proof. iIntros. iApply from_sep. iFrame. Qed.

Lemma Stackables_split k1 k2 :
  Stackables (k1 ⋅ k2) ⊢ Stackables k1 ∗ Stackables k2 .
Proof.
  rewrite /Stackables -own_op auth_frag_op.
  easy.
Qed.

Lemma Stackables_borrow_Stackable (k:lctx) q l :
  k !! l = Some q ->
  Stackables k -∗ Stackable l q ∗ (Stackable l q -∗ Stackables k).
Proof.
  iIntros (Hklq) "Hk".
  rewrite <- (insert_id k l q); try easy.
  rewrite <- insert_delete_insert.
  rewrite insert_singleton_op.
  2:{ rewrite lookup_delete //. }
  iDestruct "Hk" as "[? ?]". iFrame.
  iIntros.
  iApply Stackables_union.
  iFrame.
Qed.

Lemma Stackables_borrow_Stackable' (k:lctx) l :
  l ∈ dom k ->
  Stackables k ⊢ ∃ q, Stackable l q ∗ (Stackable l q -∗ Stackables k).
Proof.
  iIntros.
  iExists (k !!! l).
  iApply Stackables_borrow_Stackable; last iFrame.
  apply @lookup_lookup_total. apply elem_of_dom. set_solver.
Qed.

Lemma exploit_Stackables maxsize k σ r k' :
  interp true maxsize k σ r ∗ Stackables k' -∗
  ⌜forall l, k' !! l = Some 1%Qp -> l ∉ dom k⌝.
Proof.
  iIntros "[Hi Hn]".
  iIntros (l Hl).
  iApply (exploit_Stackable_full with "[Hi //]").
  iDestruct (Stackables_borrow_Stackable k' l _ with "[$]") as "(? & ?)".
  iFrame.
  Unshelve. easy.
Qed.

Lemma exploit_Stackables_full maxsize k σ r locs :
  interp true maxsize k σ r ∗ ([∗ set] l ∈ locs, Stackable l 1%Qp) -∗
  ⌜locs ∩ dom k = ∅⌝.
Proof.
  iIntros "(Hi & ?)".
  iAssert (⌜∀ l, l ∈ locs -> l ∉ dom k⌝)%I with "[-]" as "%Hl".
  { iIntros (l ?).
    iDestruct (big_sepS_elem_of_acc  _ locs l with "[$]") as "(?& _)"; eauto.
    iApply (exploit_Stackable_full with "[Hi] [$]"). iFrame. }
  iPureIntro.
  set_solver.
Qed.

Definition gg (r:gset loc) : gmap loc Qp :=
  gset_to_gmap 1%Qp r.

Lemma dom_gg r : dom (gg r) = r.
Proof. apply dom_gset_to_gmap. Qed.

Lemma interp_shift_nofree maxsize k σ l1 l2 :
  (interp false maxsize k σ (l1 ∪ l2) ⊢ |==>
  (* l2 is now in the context *)
     (interp false maxsize (kmerge k (gg l2)) σ l1) ∗
     (* The capacity to restore the old context. *)
     (∀ σ' l1', ⌜dom σ ⊆ dom σ'⌝ -∗ interp false maxsize (kmerge k (gg l2)) σ' l1' ==∗
      interp false maxsize k σ' (l1' ∪ l2))).
Proof.
  iIntros  "Hi".
  destruct_interp "Hi".
  iSplitL.
  { iExists θ.
    iFrame.
    iPureIntro.
    rewrite dom_kmerge dom_gg.
    split_and !; eauto.
    1,2:eapply correct_weak; eauto; set_solver.
    eapply related_weak; eauto; set_solver. }
  { iModIntro.
    iIntros (? ? Hdom) "[%θ' [%Hσ' [%Hθ' [%Hvθ' [%Hσθ' [? [Hk [Hm ?]]]]]]]]".
    iFrame.
    iModIntro.
    iFrame "∗ %".
    iExists θ'. iFrame.
    iPureIntro.
    split_and !.
    1,2:eapply correct_weak; eauto; rewrite dom_kmerge dom_gg; set_solver.
    eauto.
    eapply related_weak; eauto; rewrite dom_kmerge dom_gg; set_solver. }
Qed.

Lemma interp_nofree maxsize k σ l :
  interp true maxsize k σ l ⊢
  interp false maxsize k σ l ∗
  (∀ σ' (l':gset loc), interp false maxsize k σ' l' -∗ interp true maxsize k σ' l').
Proof.
  iIntros "Hi".
  destruct_interp "Hi".
  iSplitR "Hctx".
  { iExists _. iFrame. eauto. }
  iIntros (? ?) "[%θ' [%Hσ' [%Hvθ' [%Hθ' [%Hσθ' [? [Hk [Hm ?]]]]]]]]".
  iFrame.
  iExists θ'. iFrame "∗ %".
Qed.

(* LATER facto *)
Lemma interp_shift b maxsize k σ l1 L2 l2 :
  l2 = dom L2 ->
  (interp b maxsize k σ (l1 ∪ l2) ∗ Stackables L2 ⊢ |==>
          (* l2 is now in the context *)
          (interp b maxsize (kmerge k L2) σ l1) ∗
          (* The capacity to restore the old context. *)
          (∀ σ' l1', ⌜dom σ ⊆ dom σ'⌝ -∗ interp b maxsize (kmerge k L2) σ' l1' ==∗
                      Stackables L2 ∗ interp b maxsize k σ' (l1' ∪ l2))).
Proof.
  iIntros (HL2) "He".
  destruct b.
  { iDestruct (exploit_Stackables with "He") as "%Hls1".
    iDestruct "He" as "[Hi Hctx1]".
    destruct_interp "Hi".
    iSplitL.
    { iExists θ.
      iFrame.
      iDestruct (own_update_2 with "[$] [$]") as ">?"; last iFrame.
      { rewrite auth_frag_op comm //. }
      iPureIntro.
      rewrite dom_kmerge -HL2.
      split_and !; eauto.
      1,2:eapply correct_weak; eauto; set_solver.
      eapply related_weak; eauto; set_solver. }
    { iModIntro.
      iIntros (? ? Hdom) "[%θ' [%Hσ' [% [%Hθ' [%Hσθ' [? [Hk [Hm ?]]]]]]]]".
      rewrite auth_frag_op own_op.
      iDestruct "Hm" as "[? ?]".
      iFrame.
      iModIntro.
      iFrame "∗ %".
      iExists θ'. iFrame "∗ %".
      iPureIntro.
      split; last split.
      1,2:eapply correct_weak; eauto; rewrite dom_kmerge -HL2; set_solver.
      eapply related_weak; eauto; rewrite dom_kmerge -HL2; set_solver. } }
  { iDestruct "He" as "[Hi Hctx1]".
    destruct_interp "Hi".
    iSplitR "Hctx1".
    { iExists θ.
      iFrame.
      iPureIntro.
      rewrite dom_kmerge -HL2.
      split_and !; eauto.
      1,2:eapply correct_weak; eauto; set_solver.
      eapply related_weak; eauto; set_solver. }
    { iModIntro.
      iIntros (? ? Hdom) "[%θ' [%Hσ' [% [%Hθ' [%Hσθ' [? [Hk [Hm ?]]]]]]]]".
      iFrame.
      iModIntro.
      iFrame "∗ %".
      iExists θ'. iFrame "∗ %".
      iPureIntro.
      split_and !; eauto.
      1,2:eapply correct_weak; eauto; rewrite dom_kmerge -HL2; set_solver.
      eapply related_weak; eauto; rewrite dom_kmerge -HL2; set_solver. } }
Qed.

(* ------------------------------------------------------------------------ *)
(* We now prove that [interp] can indeed be used with our wp. *)

Lemma interp_weak_roots b maxsize ls1 ls2 k σ :
  ls1 ⊆ ls2 ->
  interp b maxsize k σ ls2 ⊢ interp b maxsize k σ ls1.
Proof.
  iIntros (?) "Hi".
  destruct_interp "Hi".
  iExists θ. iFrame.
  iPureIntro.
  assert (dom k ∪ ls1 ⊆ dom k ∪ ls2) as Hik by set_solver.
  split_and !; eauto.
  { apply (correct_weak Hσ); set_solver. }
  { apply (correct_weak Hθ); set_solver. }
  { apply (related_weak Hσθ); set_solver. }
Qed.

Lemma interp_gc b maxsize σ σ' k l :
  gc (dom k∪l) σ σ' ->
  interp b maxsize k σ l ⊢ interp b maxsize k σ' l.
Proof.
  iIntros (?) "Hi".
  destruct_interp "Hi".
  iExists θ.
  iFrame "%". iFrame.
  erewrite gc_dom; try iFrame; try eauto.
  iPureIntro. generalize Hσ. intros [].
  eauto using gc_preserves_correct,gc_preserves_related.
Qed.

(* ------------------------------------------------------------------------ *)

(* A space credit, or diamond, is represented by a fragmentary element
   of the monoid Auth(Nat). The assertion ♢1 can be thought of as the
   ownership of one word of available space in the heap. *)

Definition diamond (n : ugfrac) : iProp Σ :=
  own γdia (◯ n).

Local Notation "♢ n" := (diamond n)%I%Qz (at level 20) : bi_scope.

Lemma diamonds_split (n m : ugfrac) :
  ♢ (n + m) -∗ ♢ n ∗ ♢ m.
Proof.
  rewrite /diamond -own_op -auth_frag_op ugfrac_op //.
Qed.

Lemma diamonds_join n m :
  ♢ n ∗ ♢ m -∗ ♢ (n + m).
Proof.
  rewrite /diamond -own_op auth_frag_op //.
Qed.

Lemma diamond_split_iff n m  :
  (♢ (n + m))%I ≡ (♢ n ∗ ♢ m)%I.
Proof.
  iSplit.
  { iApply diamonds_split. }
  { iApply diamonds_join. }
Qed.

Lemma diamonds_zero :
  (⊢ |==> ♢ 0)%I.
Proof.
  iApply own_unit.
Qed.

(* ------------------------------------------------------------------------ *)
(* interp_free *)

(* LATER MOVE *)
Lemma ugfrac_update_incr (γ : gname) (m k : ugfrac) :
  own γ (● m)%Qz -∗
  |==> own γ (● (m ⋅ k)%Qz) ∗ own γ (◯ k).
Proof.
  iIntros. rewrite -own_op.
  iApply (own_update with "[$]").
  apply auth_update_alloc.
  apply ugfrac_local_update.
  rewrite right_id ugfrac_op //.
Qed.

Lemma interp_free maxsize (k:lctx) (σ:store) ls bs (l:loc) (b:store.block) :
  l ∉ ls ->
  dom bs ⊆ {[l]} →
  interp true  maxsize k σ ls ∗ Stackable l 1%Qp ∗ l ↦ b ∗ l ↤ bs ⊢ |==>
  interp true maxsize k σ ls ∗ ♢(size_block b) ∗ †l.
Proof.
  iIntros (Hl ?) "[Hi [Hnctx [Hmapsto Hmapsfrom]]]".
  iDestruct (exploit_Stackable_full with "Hi Hnctx") as %?.
  destruct_interp "Hi".
  iDestruct (exploit_mapsto with "Hph Hmapsto") as %?.
  iDestruct (ph_free_singleton with "[Hph Hmapsfrom Hmapsto]") as ">[Hi [? %Ho]]".
  2:iFrame. set_solver.

  (* Perform a ghost update to create new diamonds, so as to reflect the
     fact that the available space in the heap increases. *)
  iMod (ugfrac_update_incr _ _ (size_block b) with "Hdiams") as "[? ?]".
  rewrite ugfrac_op -nat_to_Qz_add.
  erewrite <- available_dealloc ; [|by destruct Hθ | eauto].
  iModIntro. iFrame.
  iExists _.
  iFrame. iFrame "%".
  iPureIntro. split_and !; eauto.
  { eapply free_preserves_correct; eauto; set_solver. }
  { eapply free_preserves_valid_store; eauto. }
  { eapply free_preserves_related; eauto; set_solver. }
Qed.
End Interp.

Global Notation "♢ n" := (diamond n)%I%Qz (at level 20) : bi_scope.

Global Instance spacelambda_spacelambdaGS `{interpGS Σ} : spacelambdaGS Σ.
Proof.
  apply (GlaneurGS _ interp Stackables).
  { eapply interp_shift. }
  { eapply interp_nofree. }
  { eapply interp_shift_nofree. }
  { apply interp_weak_roots. }
  { apply interp_gc. }
Defined.

Section MoreInterp.
Context `{iG:!interpGS Σ}.

Lemma exploit_mapsto b maxsize l q vs k σ L :
  l ∈ L ->
  interp b maxsize k σ L ∗ l ↦{q} BBlock vs ⊢ ⌜σ !! l = Some (BBlock vs)⌝.
Proof.
  iIntros (Hl) "[Hi ?]".
  destruct_interp "Hi".
  iDestruct (exploit_mapsto with "[$] [$]") as "%Hvs".
  iPureIntro.
  assert (l ∈ (dom k ∪ L)) as Hkl by set_solver.
  now rewrite (related_read_root Hkl Hσθ Hvs).
Qed.

(* Another way of saying interp_free *)
Lemma logical_free L bs (l:loc) (blk:store.block) :
  l ∉ L ->
  dom bs ⊆ {[l]} →
  (Stackable l 1%Qp ∗ l ↦ blk ∗ l ↤ bs) =[true | L]=∗ (♢(size_block blk) ∗ †l).
Proof. intros. iIntros. iApply interp_free; eauto. iFrame. Qed.

Lemma Stackable_confront l1 l2 p1 :
  Stackable l1 p1 ∗ Stackable l2 1%Qp -∗ ⌜l1 ≠ l2⌝.
Proof.
  iIntros "(? & ?)".
  unfold Stackable.
  iDestruct (own_valid_2 with "[$] [$]") as "%Hv".
  iPureIntro.
  apply auth_frag_valid_1 in Hv. simpl in *.
  intros ?. subst.
  rewrite singleton_op in Hv.
  apply singleton_valid in Hv.
  rewrite frac_valid frac_op in Hv.
  eapply Qp_not_add_le_l. eauto.
Qed.

Lemma Stackables_confront_Stackable k l L :
  Stackables k ∗ Stackable l 1%Qp =[true | L]=∗⌜l ∉ dom k⌝ ∗ Stackables k ∗ Stackable l 1%Qp.
Proof.
  iIntros "(Hxs & Hx)". iIntros (? k' ?) "Hi".
  destruct_interp "Hi".
  iDestruct (own_valid_3 with "Hxs Hx Hk") as "%Hv".
  iModIntro. iFrame.
  iSplitL. iExists _. iFrame. iFrame "%".
  iPureIntro.
  rewrite -auth_frag_op comm in Hv.
  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv & _).
  rewrite lookup_included in Hv. specialize (Hv l).
  intros E. rewrite elem_of_dom in E. destruct E as (e,Hkl).
  rewrite lookup_op lookup_singleton Hkl -Some_op in Hv.
  destruct (is_Some_included _ _ Hv) as (xl,Hxl); try easy.
  rewrite Hxl in Hv. apply Some_included in Hv.
  rewrite lookup_gset_to_gmap_Some in Hxl. destruct Hxl as (?&Hxl). subst xl.
  destruct Hv as [Hv|Hv].
  { apply id_free_l in Hv; try easy. apply _. }
  { apply frac_included in Hv.
    eapply exclusive_r; try apply frac_full_exclusive.
    rewrite frac_valid. apply Qp_lt_le_incl. eauto. }
Qed.

(* ------------------------------------------------------------------------ *)
(* We lift some lemmas from ph *)

Lemma mapsfrom_confront b l1 q1 ls1 l2 q2 ls2 L :
  (1 < q1 + q2)%Qz ->
  l1 ↤{q1} ls1 ∗ l2 ↤{q2} ls2 =[b | L]=∗
  l1 ↤{q1} ls1 ∗ l2 ↤{q2} ls2 ∗ ⌜l1 ≠ l2⌝.
Proof.
  iIntros (?) "[H1 H2]". iIntros (? ? ?) "Hi".
  destruct_interp "Hi".
  iDestruct (ph_mapsfrom_confront with "[$] H1 H2") as "%E".
  easy.
  iFrame. iSplitL; try easy. iExists _. now iFrame.
Qed.

Lemma mapsfrom_cleanup b l l' q ls L:
  l ↤{q} ls ∗ †l' =[b | L]=∗
  l ↤{q} (ls ⊎ {[-l'-]}).
Proof.
  iIntros  "(Hf & ?)".  iIntros (? ? ?) "Hi".
  destruct_interp "Hi".
  iDestruct (exploit_mapsfrom_dom_large with "[$] [$]") as "%Hd".
  iMod (ph_cleanup_singleton _ l with "[$]") as "[? H0]".
  { easy. }
  iDestruct (mapsfrom_join with "Hf H0") as "?". rewrite right_id_L.
  iFrame. iExists _. iFrame. by iFrame "%".
Qed.

End MoreInterp.

Module Initialization.

  Definition interpΣ : gFunctors :=
    #[ invΣ;
       Initialization.phΣ loc store.block;
       GFunctor (authR ugfracUR);
       GFunctor (authUR (gmapUR loc fracR)) ].

  (* The difference between the *PreG and *G is the presence of the names
     of ghost cells. (ie. gname) *)
  Class interpPreG (Σ : gFunctors) :=
  { piinvgs :> invGpreS Σ;
    piphg :> Initialization.phPreG loc store.block Σ;
    pidiamonds :> inG Σ (authR ugfracUR);
    pictx :> inG Σ (authUR (gmapUR loc fracR));
    }.

  Global Instance subG_interpPreG Σ :
    subG interpΣ Σ → interpPreG Σ.
  Proof. solve_inG. Qed.

  Global Instance interpPreG_interpΣ : interpPreG interpΣ.
  Proof. eauto with typeclass_instances. Qed.

  Lemma interp_init `{!interpPreG Σ, hinv:!invGS Σ} b (maxsize : nat) :
    ⊢ |==> ∃ hi : interpGS Σ, ⌜@iinvgs Σ hi = hinv⌝ ∗
    interp b maxsize ∅ ∅ ∅ ∗ ♢maxsize.
  Proof.
    intros.
    iIntros. rewrite /interp.
    iMod Initialization.ph_init as "[%Iph ?]".

    iMod (own_alloc (● gset_to_gmap 1%Qp (dom (∅:store)))) as (γctx) "Hctx".
    { rewrite auth_auth_valid. done. }

    iMod (own_unit (authUR (gmapUR loc fracR)) γctx) as "OwnEmpty".
    iMod (own_update _ _ (◯ ∅) with "OwnEmpty").
    { easy. }

    iMod (@own_alloc _ (authR ugfracUR) _ (● (nat_to_Qz (available maxsize ∅):ugfrac) ⋅ ◯ (nat_to_Qz (available maxsize ∅):ugfrac))) as (γdia) "[? Hdia]".
    { rewrite auth_both_valid. done. }

    iExists (@InterpG Σ hinv _ _ _ γctx γdia).
    iSplitR; try easy.
    iSplitR "Hdia".
    2:{ rewrite available_init /diamond //. }

    iExists _. destruct b; iFrame.
    all: rewrite dom_empty_L left_id_L;
      eauto using valid_store_init,correct_init, related_reflexive.
  Qed.

End Initialization.

Module FullInitialization.
  Export Initialization.
  (* This cannot be global as we want to keep Σ as a parameter:
     we thus do _not_ want coq to use interpΣ *)

  #[export] Instance interpGS_interpΣ : interpGS interpΣ.
  Proof. repeat (constructor; eauto with typeclass_instances). Qed.
End FullInitialization.
