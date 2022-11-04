From stdpp Require Import decidable binders gmultiset.
From iris Require Import proofmode.proofmode algebra.gmap.
From spacelambda Require Import more_space_lang wp_all wp_spec triple.
From spacelambda.language Require Import notation closure.
From spacelambda.examples Require Import tactics utils vector vector_amortized.
From spacelambda.examples.list Require Import list iter_clo.

Import language.
Import notation.
Import ListsOf.

Context `{!interpGS Σ}.

Definition VectorOf {A} (R : A -> val -> iProp Σ) (xs : list (A * Qp)) (l : loc) : iProp Σ :=
  ∃ (vs : list (val * Qp)),
    VectorAm vs l
  ∗ ([∗ list] x; v ∈ xs; vs, R x.1 v.1 ∗ ⌜x.2 = v.2⌝ ∗ v.1 ↤? ∅ ∗ vStackable v.1 1%Qp)%I.

Record graph := {
  neighbors_at : list (list nat);
  wf_neighbors_at : forall i l, l ∈ neighbors_at -> i ∈ l -> i < length neighbors_at
}.

Global Instance graph_size : Size graph := λ g, length (neighbors_at g).

Definition has_edge (G : graph) i j := j ∈ neighbors_at G !!! i.

Definition add_11 (l : list nat) := (λ n, (n, (1%Qz, 1%Qp))) <$> l.
Definition add_1 (l : list (list nat)) := (λ l, (add_11 l, 1%Qp)) <$> l.

Definition isGraph (G : graph) (g : loc) : iProp Σ :=
  VectorOf
    (fun L v => ∃ l, ⌜v=(#l)%V⌝ ∗ ListOf (fun (n : nat) v => ⌜v = (^n)%V⌝) L l)%I
    (add_1 (neighbors_at G))
    g.

Definition number_of_edges (G : graph) := sum_list_with length (neighbors_at G).

Inductive reachable (G : graph) : nat -> nat -> Prop :=
  | reachable_self a : a < size G -> reachable G a a
  | reachable_edge a b c : reachable G a b -> has_edge G b c -> reachable G a c.

Lemma reachable_ind_unary (G : graph) (P : nat -> Prop) (src : nat) :
  (forall i j, has_edge G i j -> P i -> P j) ->
  (forall i j, reachable G i j -> P i -> P j).
Proof.
  intros H i j ij.
  induction ij; firstorder.
Qed.

Lemma edge_bounds G i j : has_edge G i j -> i < size G /\ j < size G.
Proof.
  destruct G as [l wf].
  rewrite /has_edge /= /size /graph_size /= //.
  change (j ∈ l !!! i → i < length l ∧ j < length l).
  rewrite list_lookup_total_alt.
  destruct (l !! i) eqn:Eli; rewrite /=.
  - intros Hg; split.
    + apply lookup_lt_is_Some_1; auto.
    + pose proof (elem_of_list_lookup_2 _ _ _ Eli).
      eapply wf; eauto.
  - inversion 1.
Qed.

Lemma edge_inbound G i j : has_edge G i j -> i < size G.
Proof.
  apply edge_bounds.
Qed.

Lemma edge_outbound G i j : has_edge G i j -> j < size G.
Proof.
  apply edge_bounds.
Qed.

Definition count `{EqDecision A} (x : A) (l : list A) : nat := length (filter (eq x) l).

Section count_facts.

Context `{EqDecision A}.
Context `{Inhabited A}.

Lemma count_some (x : A) (l : list A) (i : nat) :
  i < length l ->
  l !!! i = x ->
  1 ≤ count x l.
Proof.
  rewrite /count.
  revert i; induction l as [ | b l ]; intros i Hi L. inversion Hi.
  destruct i as [ | i ].
  - simpl in *. subst.
    rewrite filter_cons_True /= //; lia.
  - simpl in *.
    rewrite !filter_cons.
    destruct (decide _) as [-> | n]; simpl; erewrite IHl; eauto; lia.
Qed.

Lemma count_remove (x y : A) (l : list A) (i : nat) :
  x ≠ y ->
  i < length l ->
  l !!! i = x ->
  count x l = count x (<[i:=y]> l) + 1.
Proof.
  rewrite /count.
  revert i; induction l as [ | b l ]; intros i xy Hi L. inversion Hi.
  destruct i as [ | i ].
  - simpl in *. subst.
    rewrite filter_cons_True /= // filter_cons_False /= //; lia.
  - simpl in *.
    rewrite !filter_cons.
    destruct (decide _) as [-> | n]; simpl; erewrite IHl; eauto; lia.
Qed.

Lemma count_replicate (x : A) n : count x (replicate n x) = n.
Proof.
  unfold count.
  induction n. easy.
  rewrite /= filter_cons_True // /=.
  congruence.
Qed.

Lemma count_true_false l : count true l + count false l = length l.
Proof.
  unfold count.
  induction l as [ | [ | ] l ]; auto; rewrite !filter_cons; simpl; lia.
Qed.

End count_facts.

(* [neighbors] is the list of neighbors remaining to be processed *)

Record inv (G : graph) (src : nat) (marked : list bool) (stack neighbors : list nat) (measure : nat) := {
  inv_length_marked : length marked = size G;
  inv_source_node : src < size G;
  inv_source : marked !!! src = true;
  inv_stack : forall i, i ∈ stack -> i < size G /\ marked !!! i = true;
  inv_true_reachable : forall i, i < size G -> marked !!! i = true -> reachable G src i;
  inv_true_edges : forall i j, marked !!! i = true -> has_edge G i j -> i ∈ stack \/ marked !!! j = true \/ j ∈ neighbors;
  inv_measure : measure = count false marked + length stack;
  inv_stack_nodup : NoDup stack; (* required for length stack <= size G (< size G requires a little more) *)
}.

Lemma inv_stack_bound G a marked stack neigh measure :
  inv G a marked stack neigh measure ->
  length stack <= size G.
Proof.
  intros H.
  destruct H.
  rewrite -size_list_to_set //.
  transitivity (length (seq 0 (size G))). 2: now rewrite seq_length.
  rewrite -size_list_to_set. 2: apply NoDup_seq.
  apply subseteq_size.
  intros i.
  rewrite !elem_of_list_to_set =>Hi.
  destruct (inv_stack0 i Hi).
  rewrite elem_of_seq.
  lia.
Qed.

Tactic Notation "assert_specialize" hyp(H) :=
  match type of H with
    forall _ : ?a, _ =>
    let Ha := fresh in
    assert (Ha : a); [ | specialize (H Ha); clear Ha ]
  end.

Lemma initial_measure n a : a < n -> count false (<[a:=true]> (replicate n false)) = n - 1.
Proof.
  intros Ha.
  pose proof count_replicate false n.
  pose proof count_remove false true (replicate n false) a as R.
  assert_specialize R. easy.
  assert_specialize R. now rewrite replicate_length.
  assert_specialize R. now rewrite lookup_total_replicate_2.
  lia.
Qed.

Lemma inv_init G a : a < size G -> inv G a (<[a:=true]> (replicate (size G) false)) [a] [[]]%T (size G).
Proof.
  assert (Htrue : forall i, i < size G -> <[a:=true]> (replicate (size G) false) !!! i = true -> i = a). {
    intros i Hi.
    destruct (decide (a = i)) as [-> | n].
    + rewrite list_lookup_total_insert // replicate_length. lia.
    + rewrite list_lookup_total_insert_ne // lookup_total_replicate_2; lia.
  }

  split.
  - rewrite insert_length replicate_length //.
  - auto.
  - apply list_lookup_total_insert.
    rewrite replicate_length; lia.
  - intros i. rewrite elem_of_list_singleton =>->.
    rewrite list_lookup_total_insert // replicate_length; lia.
  - intros i Hi Ci. apply Htrue in Ci; auto. subst. constructor. auto.
  - intros i Hi Ci ij. apply Htrue in Ci. 2: now eapply edge_inbound; eauto.
    left. apply elem_of_list_singleton, Ci.
  - rewrite initial_measure /= //. lia.
  - apply NoDup_singleton.
Qed.

Lemma inv_push_and_mark G a marked stack E i j measure :
  marked !!! i = true ->
  has_edge G i j ->
  inv G a marked stack (j :: E) measure ->
  marked !!! j = false ->
  inv G a (<[j:=true]> marked) (stack ++ [j]) E measure.
Proof.
  intros Ci ij [] H0.
  assert (i < size G) as Ni by now eapply edge_inbound; eauto.
  assert (j < size G) as Nj by now eapply edge_outbound; eauto.
  assert (j < length marked) by now rewrite -inv_length_marked0 in Nj.
  split; auto.
  - rewrite insert_length //.
  - destruct (decide (a = j)) as [->|aj].
    + rewrite list_lookup_total_insert //.
    + rewrite list_lookup_total_insert_ne //.
  - intros k. rewrite elem_of_app. intros [Hk | jk].
    + destruct (inv_stack0 k); auto. split; auto.
      destruct (decide (k = j)) as [->|kj].
      * rewrite list_lookup_total_insert //.
      * rewrite list_lookup_total_insert_ne //.
    + apply elem_of_list_singleton in jk; subst. split.
      * eapply edge_outbound; eauto.
      * rewrite list_lookup_total_insert //.
  - intros k Hk.
    destruct (decide (k = j)) as [->|kj].
    * rewrite list_lookup_total_insert //. intros _.
      apply reachable_edge with i; auto.
    * rewrite list_lookup_total_insert_ne //.
      apply inv_true_reachable0; auto.
  - intros ii k.
    destruct (decide (ii = j)) as [->|iij].
    + intros _ _. left. apply elem_of_app. right. left.
    + rewrite list_lookup_total_insert_ne //.
      intros Hi ik.
      specialize (inv_true_edges0 ii k Hi ik).
      destruct inv_true_edges0 as [HE | [HE | HE] ].
      * left. apply elem_of_app. left; auto.
      * right. left. destruct (decide (j = k)) as [->|jk].
        -- rewrite list_lookup_total_insert //.
        -- rewrite list_lookup_total_insert_ne //.
      * inversion HE; subst.
        -- rewrite list_lookup_total_insert //. auto.
        -- auto.
  - rewrite inv_measure0 (count_remove _ true _ j) // app_length /=. lia.
  - rewrite -Permutation_cons_append. constructor; auto.
    intros Hj. destruct (inv_stack0 j Hj). congruence.
Qed.

Definition array_fill : val :=
  μ: "self", [["dst", "v", "i", "n"]],
    let: "neq" := "n" '- "i" in
    if: "neq" then
      "dst".["i"] <- "v";;
      let: "i" := "i" '+ ^1 in
      "self" [["dst", "v", "i", "n"]]
    else
      ()%V.

Lemma array_fill_spec_from_unit_to_nat `{!interpGS Σ} (dst : loc) (v i n : nat) :
  CODE (array_fill [[#dst, ^v, ^i, ^(i + n)]])
  SOUV {[dst]}
  PRE (dst ↦ BBlock (replicate i (^v)%V ++ replicate n ()%V))
  POST (fun _ : unit => dst ↦ BBlock (replicate (i + n) (^v)%V)).
Proof.
  iIntros "Hdst".
  iInduction n as [ | len ] "IH" forall (i).
  - wps_call.
    wps_bind. wps_val.
    wps_if. rewrite decide_False. 2:lia.
    wps_val. rewrite Nat.add_0_r. done.
  - wps_call.
    wps_bind. wps_val.
    wps_if. rewrite decide_True. 2:lia.
    wps_bind. wps_store.
    replace (<[i:=^v]> (replicate i ^v ++ () :: replicate len ()))%V
      with  (replicate (i + 1) ^v ++ replicate len ())%V
      by rewrite insert_app_r_alt ?replicate_length ?Nat.sub_diag /= //
           replicate_plus -app_assoc /= //.
    wps_bind. wps_val.
    fold array_fill.
    change (enc (i + 1)) with (^(i + 1))%V.
    replace (^(i + S len))%V with (^(i + 1 + len))%V by (f_equal; lia).
    iSpecialize ("IH" $! (i + 1) with "[$]").
    iApply (wps_mono with "[IH]").
    iApply "IH".
    replace (i + 1 + len)%nat with (i + S len)%nat by lia.
    auto.
Unshelve.
  now constructor.
  now rewrite app_length replicate_length /=; lia.
Qed.

Definition reachable_imperative : val :=
  (* let reachable_imperative g a b = *)
  λ: [["g", "a", "b"]],
    (* let n = Graph.nb_nodes g in *)
    let: "n" := vector_size [["g"]] in
    (* let c = Array.make n false in *)
    let: "c" := alloc "n" in
    array_fill [["c", 0, 0, "n"]];;
    (* let s = Stack.create() in *)
    let: "s" := vector_create [[]] in
    (* c.(a) <- true; *)
    "c".["a"] <- ^1;;
    (* Stack.push a s; *)
    vector_push [["s", "a"]];;
    (* while not (Stack.is_empty s) do *)
    (μ: "while", [["s", "c", "g"]],
        let: "not_empty" := vector_size [["s"]] in
        if: "not_empty" then
          (* let i = Stack.pop s in *)
          let: "i" := vector_pop [["s"]] in
          (* let f j = *)
          let: "f" := mk_clo BAnon ["j":binder] (
            (* if not c.(j) then begin *)
            let: "marked" := "c".["j"] in
            if: "marked" then ()%V else (
                (* c.(j) <- true; *)
                "c".["j"] <- 1;;
                (* Stack.push j s; *)
                vector_push [["s", "j"]]
              (* end); *)
              )
          (* in *)
          ) in
          (* Graph.iter_edges g i f *)
          let: "edges" := vector_get [["g", "i"]] in
          list_iter [["f", "edges"]];;
          (* done; *)
          "while" [["s", "c", "g"]]
        else ()%V) [["s", "c", "g"]];;
    (* c.(b) *)
    "c".["b"].

(** Change [wps X t Q] into two goals [wps X t R] and [∀v, Q v -∗ R v] *)
Import environments.
Ltac wps_conseq_post R :=
  match goal with
  | |- envs_entails ?Δ (wps ?X ?t ?Q) =>
      let H := fresh "Hwps_conseq_post" in
      assert (envs_entails Δ (wps X t R)) as H;
      [ | iApply (wps_mono with "[-]"); [ apply H | clear H ] ]
  end.

Tactic Notation "iAssertSpecialize" constr(iris_hyp) :=
  match goal with
  | |- context[Esnoc _ (INamed iris_hyp) (?B -∗ _)%I] =>
      iAssert B as "_tmp";
      [ | iSpecialize (iris_hyp with "_tmp"); iClear "_tmp" ]
  | |- context[Esnoc _ (INamed iris_hyp) (bi_impl ?B _)%I] =>
      (* bi_impl is the -> implication, it should not be useful with a "with" clause *)
      iAssert B as "_tmp";
      [ | iSpecialize (iris_hyp with "_tmp"); iClear "_tmp" ]
  end.

Tactic Notation "iAssertSpecialize" constr(iris_hyp) "with" constr(iris_hyps_for_the_assert) :=
  match goal with
  | |- context[Esnoc _ (INamed iris_hyp) (?B -∗ _)%I] =>
      iAssert B with iris_hyps_for_the_assert as "_tmp";
      [ | iSpecialize (iris_hyp with "_tmp") ]
  end.

Definition HIDDEN {A : Type} {x : A} := x.

Tactic Notation "iHide" constr(iris_hyp) :=
  match goal with
  | |- context[Esnoc ?G (INamed iris_hyp) ?H] =>
      change (Esnoc G (INamed iris_hyp) H)
      with   (Esnoc G (INamed iris_hyp) (@HIDDEN _ H))
  end.

Tactic Notation "iShow" constr(iris_hyp) :=
  match goal with
  | |- context[Esnoc ?G (INamed iris_hyp) (@HIDDEN _ ?H)] =>
      change (Esnoc G (INamed iris_hyp) (@HIDDEN _ H))
      with   (Esnoc G (INamed iris_hyp) H)
  end.

Ltac cleanup_Stackable :=
  repeat
    match goal with
    | |- context[@own _ ?A _ _ (auth.auth_frag {[?l := ?q]})] =>
        change (@own _  A _ _ (auth.auth_frag {[ l :=  q]}))%I
        with (Stackable l q)
    end.

Tactic Notation "wps_weak" uconstr(r1) :=
  match goal with
  | |- envs_entails _ (wps (Some ?r2) ?t ?Q) =>
      iAssert (wps (Some r1) t Q) with "[-]" as "_tmp";
      [ | iApply (wps_weak with "_tmp") ];
      swap 1 2
  end.

Tactic Notation "wps_weak" uconstr(r1) "by" tactic(t) :=
  wps_weak r1; [ by t | ].

Definition State (G : graph) (g lmarked lstack : loc) (source : nat) (marked : list bool) (stack : list nat) (neighbors : list nat) (meas : nat) : iProp Σ :=
    lmarked ↦ BBlock (val_nat <$> (Nat.b2n <$> marked))
  ∗ ♢((size G - length stack) * 6)%nat
  ∗ $(count false marked * 11 + length stack * 4)
  ∗ VectorAm ((fun n => ((^n)%V, 1%Qp)) <$> stack) lstack
  ∗ ⌜inv G source marked stack neighbors meas⌝.

Lemma inv_end G a C meas :
  inv G a C [] [] meas ->
  forall b, b < size G -> C !!! b = true ∧ reachable G a b ∨ C !!! b = false ∧ ¬ reachable G a b.
Proof.
  intros [_ _ Ca _ Hreach Hedges].
  cut ( ∀ b : nat, reachable G a b -> b < size G → C !!! b = true). {
    intros H b Hb. destruct (C !!! b) eqn:Cb.
    - left. now specialize (Hreach b Hb Cb).
    - right. split; auto. intros Rb. specialize (H b Rb Hb). congruence.
  }
  intros b ab Hb.
  refine (reachable_ind_unary G (λ b, C !!! b = true) 42 _ a b ab Ca).
  intros i j ij Ci.
  destruct (Hedges i j Ci ij) as [F | [? | F] ]; auto; inversion F.
Qed.

Lemma inv_marked G src marked stack E i j meas :
  has_edge G i j ->
  marked !!! j = true ->
  inv G src marked stack (j :: E) meas ->
  inv G src marked stack E meas.
Proof.
  intros ij Cj []; constructor; auto.
  intros a b Ca ab.
  destruct (inv_true_edges0 a b Ca ab) as [ ? | [ ? | jE ] ]; auto.
  inversion jE; subst; intuition.
Qed.

Lemma neighbors_char G i j l : neighbors_at G !! i = Some l -> has_edge G i j <-> j ∈ l.
Proof.
  intros Hl.
  unfold has_edge.
  erewrite list_lookup_total_correct; eauto.
Qed.

Lemma neighbors_char_add_1 G i j l q : add_1 (neighbors_at G) !! i = Some (l, q) -> has_edge G i j <-> j ∈ l.*1.
Proof.
  intros Hl.
  rewrite neighbors_char; eauto.
  unfold add_1 in Hl.
  apply list_lookup_fmap_inv in Hl.
  destruct Hl as (l1 & [=->->] & ->).
  f_equal.
  induction l1; simpl; f_equal; auto.
Qed.

Lemma inv_stage_neighbors G a marked stack cur l meas :
  neighbors_at G !! cur = Some l ->
  inv G a marked (stack ++ [cur]) [] meas ->
  inv G a marked stack l (meas - 1).
Proof.
  intros Hl [].
  constructor; auto.
  - intros. apply inv_stack0. rewrite elem_of_app. auto.
  - intros i j Hi ij.
    destruct (inv_true_edges0 i j Hi ij) as [Hj | [ Hj | Hj ] ].
    + rewrite elem_of_app elem_of_list_singleton in Hj. destruct Hj as [Hj | ->]. now auto.
      right. right.
      eapply neighbors_char; eauto.
    + auto.
    + inversion Hj.
  - rewrite app_length /= in inv_measure0. lia.
  - eapply (NoDup_app stack [cur]); auto.
Qed.

Lemma Qp_Qz_1 : (1%Qp : Qz) = 1%Qz.
Proof.
  rewrite -pos_to_qz_through_nat.
  apply Qz_to_Qc_inj_iff.
  rewrite nat_to_Qz_to_Qc //.
Qed.

(** Explanation of space complexity:
 - 4: creating stack
 - size G * 6: six times the maximum size of the stack (could be refined to size G - 1)
 - size G: boolean array for marking as marked
 - 3: allocating the closure passed to list_iter
 - 3: list_iter's internal closure
*)

(** Explanation of time complexity:
 - 7 * size G: pushing all nodes on the stack
 - 4 * size G: popping all nodes

Note that we should also have O(number_of_edges G) because we iterate on all
neighbors every time, but time complexity is not accounted for in list_iter, and
this project is not about time complexity, so we only mention time complexity
here because we did for the amortized analysis for vectors (for which it was
useful to check that our implementation for amortized space complexity was not
at the expense of time complexity). *)

Lemma reachable_imperative_spec g G (a b : nat) qg :
  a < size G ->
  b < size G ->
  CODE (reachable_imperative [[g, a, b]])
  PRE (isGraph G g ∗ Stackable g qg ∗ ♢(size G * 7 + 10) ∗ $(size G * 11))
  POST (fun (r : nat) =>
       isGraph G g ∗ Stackable g qg ∗ ♢(size G * 7 + 10)
     ∗ ⌜r = 1 /\ reachable G a b \/ r = 0 /\ ~reachable G a b⌝).
Proof.
  iIntros (Ha Hb) "(G & Sg & D & T)".
  iDestruct "G" as (locs) "(Vg & Hlocs)".
  wps_call.

  iAssert ⌜length locs = size G⌝%I as %Llocs.
  { iPoseProof (big_sepL2_length with "[$]") as "<-"; rewrite map_length //. }

  (** let n = vector_size g *)
  wps_bind_nofree.
  wps_apply vector_size_amortized_spec.
  iDestruct select (⌜_⌝ ∗ _)%I as "(%En & Vg)".
  rename v into n.

  (** let marked = alloc n *)
  wps_bind.
  wps_alloc.
  iIntros "Sg".
  rename l into lmarked.
  iDestruct select (_ ∗ _)%I as "(Pm & Sm)".

  (** array_fill marked 0 0 n *)
  wps_bind.
  wps_apply array_fill_spec_from_unit_to_nat.
  clear v.
  iIntros "(Sm & Sg)".

  (** let stack = vector_create () *)
  wps_bind.
  iDestruct (time_credit_split_alt 0 with "[$]") as "(T0 & T)". lia.
  mine 4.
  wps_apply vector_create_amortized_spec.
  rename v into lstack.
  iIntros "(Sm & Sg)".
  iDestruct select (_ ∗ _ ∗ _)%I as "(Vstack & Ss & Ps)".

  (** marked[a] <- 1 *)
  wps_bind.
  (* Fail wps_store. *)
  do 7 iStepS.
  iDestruct select (Stackables _) as "((Ss & Sm) & Sg)".
  match goal with x : unit |- _ => clear x end.

  (** stack.push(a) *)
  wps_bind.
  iDestruct (time_credit_split_alt 7 with "[$]") as "(T0 & T)". lia.
  mine 6.
  unshelve wps_apply vector_push_amortized_spec. exact 1%Qp.
  match goal with x : unit |- _ => clear x end.
  iIntros "((Ss & Sm) & Sg)".

  set (μ: _, _, _) as outer_loop.

  iRename select (♢ _)%I into "D6".
  mine ((size G - 1) * 6) as "D".

  iAssert (State G g lmarked lstack a (<[a:=true]> (replicate (length locs) false)) [a] [] (size G))%I
    with "[-D6 Ss Sm Sg Pm Ps Vg Hlocs]"
    as "Hinv".
  {
    iFrame.
    iRename select (lmarked ↦ _)%I into "Hmarked".
    iSplitL "Hmarked".
    { iExactEq = "Hmarked". iPureIntro. do 2 f_equal.
      now rewrite !list_fmap_insert !fmap_replicate //. }
    iSplitL "T".
    { iExactEq = "T". iPureIntro. do 2 f_equal.
      pose proof count_remove false true (replicate (length locs) false) a as M.
      assert_specialize M. easy.
      assert_specialize M. rewrite replicate_length Llocs //.
      assert_specialize M. rewrite lookup_total_replicate_2 // Llocs //.
      rewrite Llocs count_replicate in M.
      rewrite M Llocs /=.
      lia. }
    iPureIntro.
    rewrite Llocs. apply inv_init; auto.
  }

  iDestruct "Sm" as "(Sm1 & Sm2)".
  iDestruct "Ss" as "(Ss1 & Ss2)".
  iDestruct "Sg" as "(Sg1 & Sg2)".
  wps_bind.
  wps_context lstack.
  cleanup_Stackable.
  wps_context g.
  set (x := (_ - _)%nat); assert (x = 6)%nat as -> by lia.

  (** outer loop: induction on the measure *)
  generalize [a]; intros stack.
  generalize (<[a:=true]> (replicate (length locs) false)); intros marked.
  remember (size G) as meas eqn:Emeas.
  (* assert (0 < meas) as Hm by lia. *)
  rewrite Emeas in Llocs Ha Hb. rewrite {2}Emeas. clear Emeas.
  (* induction on "meas+1" to avoid the base case, i.e. we show
     ∀x(x>0⇒P(x-1))⇒P(x) instead of P(0)∧(∀x,P(x)⇒P(x+1)) *)
  assert (exists m, meas + 1 = m) as (m, Hm) by eauto;
  iInduction m as [ | m ] "IH" forall (meas Hm stack marked);
    [ lia | assert (m = meas) as -> by lia; clear Hm ].

  iDestruct "Hinv" as "(Hmarked & D & T & Vs & %Hinv)".
  wps_call. fold outer_loop.

  (** let not_empty = vector_size stack *)
  wps_bind_nofree.
  wps_apply vector_size_amortized_spec.
  simpl.
  rename v into nstack.
  iDestruct select (_ ∗ _)%I as "(%Heq_nstack & Vs)".

  (** if stack is empty, the outer loop ends *)
  destruct (decide (stack = [])) as [-> | stack_not_empty].
  {
    iClear "IH".
    wps_if.
    wps_val.
    iIntros "? ? ?".
    iDestruct (Stackable_join g with "[$] [$]") as "Sg".
    iDestruct (Stackable_join lstack with "[$] [$]") as "Ss".
    iDestruct (Stackable_join lmarked with "[$] [$]") as "Sm".

    (** freeing [lmarked] after load, as if there were a let *)
    iApply wps_end.

    wps_context lmarked.
    rewrite !Qp_div_2.

    (** freeing vector stack *)
    iApply (wps_esupd (A := nat) _ _ _ _ (vector_free_amortized [] lstack)).
    iFrame.
    iIntros "(Ds & ds & true)".

    (** computing return value *)
    iStepS.
    iExists _, _, _. iFrame.
    iSplit.
    { iPureIntro.
      rewrite !fmap_length //.
      destruct Hinv. lia. }
    iSplit.
    { iPureIntro.
      destruct Hinv.
      rewrite !list_lookup_total_fmap ?fmap_length; try lia.
      reflexivity. }
    iIntros "Hmarked Sm".

    (** freeing [lmarked] *)
    wps_free lmarked as "(Dm & dl')".
    wps_val.

    (** establishing spec's postcondition *)
    iFrame "Sg".
    iSplitL "Vg Hlocs". now iExists _; iFrame.
    iSplitL "D6 D Ds Dm".
    - do 3 iDestruct (diamonds_join with "[$]") as "ds".
      iExactEq = "ds". iPureIntro. f_equal.
      rew_qz.
      rewrite !fmap_length.
      destruct Hinv.
      lia.
    - iClear "T" (* here, throwing away $11 * number of unreachable nodes *).
      iPureIntro.
      eapply inv_end in Hinv; eauto.
      destruct Hinv as [ [-> H] | [-> H] ]; [left | right]; split; auto.
  }

  (** otherwise the stack is not empty *)
  wps_if.
  rewrite decide_True.
  2: now destruct stack; tauto || simpl in *; lia.

  (* using wps_let_empty instead of wps_bind, which takes more than 30 minutes *)
  (* Fail Timeout 500 wps_bind. *)
  Time simplify_substs. (* TODO: 10 seconds *)
  iApply wps_let_empty.
  reflexivity.
  {
    rewrite /locs /location_tm /=.
    apply union_least. 2:now set_solver.
    etransitivity. now apply locs_subst.
    apply union_least. now set_solver.
    etransitivity. now apply locs_subst.
    rewrite /syntax.locs /location_tm /=. rewrite locs_mk_clo.
    set_solver.
  }

  (** let [current_node] be the node we pop out *)
  destruct (@exists_last _ stack ltac:(auto)) as (stack' & current_node & ->).
  rewrite fmap_app /=.
  wps_apply vector_pop_amortized_spec.
  iDestruct (time_credit_split_alt 4 with "[$]") as "($ & T)".
  { rewrite app_length /=. lia. }
  iIntros (v1) "(-> & _ & _ & Vstack & D')".

  (** let f = our closure *)
  Time simplify_substs. (* 2.5 seconds *)
  wps_bind_nofree.

  (* we choose the specification of the closure we are allocating *)

  Definition push_and_mark_spec G g lmarked lstack a (_ : loc) (args : list val) (t : tm) (spec : iProp Σ) :=
    (∀  (marked : list bool) (stack : list nat) (neighbors : list nat) (i j meas : nat),
      ⌜args = [ ^j ]%V⌝ -∗
      ⌜has_edge G i j /\ marked !!! i = true⌝ -∗
      State G g lmarked lstack a marked stack (j :: neighbors) meas -∗
      wps (Some {[g; lstack; lmarked]}) t
      (λ _ : (),
          State G g lmarked lstack a
            (if (marked !!! j : bool) then marked else <[j := true]> marked)
            (if (marked !!! j : bool) then stack else stack ++ [j])
            neighbors meas
          ∗ spec)
    )%I.

  assert (LNE (push_and_mark_spec G g lmarked lstack a)) by lne.
  rewrite subst_subst_commut. 2: easy.

  (* we apply wps_mk_spec, which will give us the hypothesis that f satisfies push_and_mark_spec G *)
  wps_apply (wps_mk_spec (push_and_mark_spec G g lmarked lstack a)
    [("c", #lmarked)%V; ("s", #lstack)%V]
    [(1/2)%Qp : Qz; (1/2)%Qp : Qz] ).
  1-4: now compute_done.

  (** The body of the closure satisfies push_and_mark_spec *)
  {
    (* first some closure bookkeeping *)
    iModIntro.
    iIntros (l args len_args) "Spec".
    destruct args as [ | arg [ | ? ? ] ]. 1,3: now inversion len_args.
    simpl.
    clear marked Hinv.
    iIntros (marked stack E i j meas') "%Earg". inversion Earg. subst arg.
    iIntros "(%Hij & %Ci) (Hmarked & D & T & Vstack & %Hinv)".
    assert (j < length marked) as Hj. {
      destruct Hinv.
      rewrite inv_length_marked0.
      eapply edge_outbound; eauto.
    }
    assert (j < length (Nat.b2n <$> marked)) as Hj' by rewrite map_length //.

    (** if marked[j] *)
    wps_bind.
    wps_load.

    rewrite !list_lookup_total_fmap //.
    destruct (marked !!! j) eqn:Cj.
    - (** if marked[j], nothing happens *)
      wps_if.
      wps_val.
      iFrame.
      iPureIntro.
      eapply inv_marked; eauto.

    - (** otherwise *)
      wps_if.

      (** marked[j] := true *)
      wps_bind.
      wps_store.

      (** preparing invariant in advance so that we can extract space credits from invariant *)
      assert (Hinv' : inv G a (<[j:=true]> marked) (stack ++ [j]) E meas')
        by now apply inv_push_and_mark with i.
      assert (Hlen : length stack < size G). {
        apply inv_stack_bound in Hinv'.
        rewrite app_length /= in Hinv'.
        lia.
      }

      (** stack.push(j) *)
      mine 6.
      iDestruct (time_credit_split_alt 7 with "[$]") as "(T7 & T)".
      { eapply (count_some _ _ j) in Cj; auto. lia. }
      wps_apply vector_push_amortized_spec.
      unfold State.
      rewrite !list_fmap_insert !list_lookup_total_fmap //.
      rewrite fmap_app.
      iFrame.
      iSplitL "D".
      { iExactEq = "D".
        iPureIntro. f_equal. rewrite app_length /=.
        rew_qz; lia. }
      iSplit; auto.
      { iExactEq = "T". iPureIntro. f_equal.
        rewrite app_length /= (count_remove false true marked j) //.
        lia. }
  }

  (** finishing wps_mk_spec's bookkeeping *)
  simpl.
  mine 3.
  iFrame.
  rewrite /group_pointedbys Qp_to_Qz_mul_distr Qp_Qz_1.
  change ((1 * / 2)%Qz) with ((1 / 2)%Qz).
  rewrite -{4 5}(Qz_div_2 1).
  rewrite /=.
  iDestruct (mapsfrom_split_empty with "Ps") as "(Ps1 & $)".
  iDestruct (mapsfrom_split_empty with "Pm") as "(Pm1 & $)".
  iIntros (lclosure) "(Pc & Sc & Hclosure)".

  (** let edges = neighbors of current_node *)
  wps_bind.
  iPoseProof (big_sepL2_length with "[$]") as "%lenadj".
  assert (current_node < length locs) as li.
  { rewrite -lenadj map_length.
    destruct Hinv.
    specialize (inv_stack0 current_node).
    assert_specialize inv_stack0.
    { apply elem_of_app. right. left. }
    destruct inv_stack0 as [Hcur _].
    apply Hcur.
  }

  Time wps_apply vector_get_amortized_spec. (* TODO 8 sec *) assumption.
  iDestruct select (_ ∗ _)%I as "(-> & Vg)".
  iIntros "Sc".

  (** extracting the neighbors from the graph's vector (some bookkeeping is due
  to the more general VectorOf instead of a custom version) *)
  pose (R_isnat := λ n v, ⌜v = (^n)%V⌝%I : iProp Σ).
  fold R_isnat.
  pose proof lookup_lt_is_Some_2 _ _ li as ((v_ & qn) & Eneighbors).
  set (ll := add_1 _); assert (current_node < length ll) as lli by now subst ll; congruence; subst ll.
  pose proof lookup_lt_is_Some_2 _ _ lli as ((neighbors_qs, q_) & Hneighbors_qs).
  iDestruct (big_sepL2_lookup_acc with "Hlocs") as "((Hneighbors & %Eq_ & Pn & Sn) & Hlocs_hole)"; eauto.
  simpl in Eq_; subst q_.
  iDestruct "Hneighbors" as (lneighbors) "(%Heq & Hneighbors)".
  simpl in Heq; subst v_; simpl.

  (** iteration on current_node's neighbors *)
  wps_bind.
  wps_context lclosure.
  wps_context lneighbors.

  pose (I := fun (remaining_neighbors : list nat) => (
      Spec 1 [((#lmarked)%V, (1 / 2)%Qz); ((#lstack)%V, (1 / 2)%Qz)] (push_and_mark_spec G g lmarked lstack a) lclosure
    ∗ ⌜Forall (has_edge G current_node) remaining_neighbors⌝
    (* Stackables required because closure needs to be shown to not free g *)
    ∗ Stackable g (qg / 2)%Qp
    ∗ Stackable lstack (1 / 2)%Qp
    ∗ Stackable lmarked (1 / 2)%Qp
    ∗ ∃ stack marked,
      ⌜marked !!! current_node = true⌝
      ∗ State G g lmarked lstack a marked stack remaining_neighbors (meas - 1)
    )%I : iProp Σ).

  iPoseProof (iter_spec_remaining I R_isnat neighbors_qs lneighbors lclosure 1)
    as "-#iter"; [ auto | ].
  mine 2 as "D2".
  erewrite list_lookup_total_correct; [ | eassumption ]; simpl.

  iAssertSpecialize "iter" with "[-IH Pm1 Ps1 Vg Hlocs_hole Pn iter D']".

  iSplit.
  { (** each iteration of the closure preserves the invariant *)
    iModIntro.
    iIntros (neighbor v_ remaining_neighbors) "(I & Rxy)".
    iDestruct "Rxy" as "->".
    iDestruct "I" as "(Hclosure & %Hedges & Sg & Ss & Sm & Hstate)".
    iApply (wpc_call_spec with "Hclosure").
    now change ([(^neighbor)%V : tm]) with (tm_val <$> [(^neighbor)%V]); reflexivity.
    reflexivity.
    iIntros (body) "Hclosure".
    iDestruct "Hstate" as (stack_ marked_) "Hstate".
    iDestruct "Hstate" as "(%Hmarked_cur & Hmarked & D & T & Vstack & %Hinv_)".
    iSpecialize ("Hclosure" $! marked_ stack_ remaining_neighbors current_node neighbor (meas - 1)).
    iAssertSpecialize "Hclosure". easy.
    iAssertSpecialize "Hclosure". now iPureIntro; split; auto; inversion Hedges; subst; auto.
    iSpecialize ("Hclosure" with "[$Vstack $Hmarked $D $T]"); auto.
    rewrite -(wps_eq _ _ (Some _)).
    wps_context g.
    wps_context lstack.
    wps_context lmarked.
    wps_weak {[g; lstack; lmarked]} by set_solver.
    iApply (wps_mono with "Hclosure").
    iIntros ([]) "(Hstate & Hclosure) Sm Ss Sg". iSplit. done.
    iFrame.
    iSplit. now inversion Hedges; subst; auto.
    iExists _, _. iFrame.
    iPureIntro.
    destruct (marked_ !!! neighbor) eqn:E; auto.
    destruct (decide (neighbor = current_node)) as [-> | n].
    - rewrite list_lookup_total_insert //; congruence.
    - rewrite list_lookup_total_insert_ne //.
  }

  { (** we establish the invariant before list iter *)
    iFrame.
    iSplit.
    * (* the list only contains neighbors *)
      iPureIntro.
      apply Forall_forall; intros j Hj.
      eapply neighbors_char_add_1; eauto.
    * iExists stack', marked.
      iFrame.
      iSplit.
      { iPureIntro.
        inversion Hinv.
        apply inv_stack0. rewrite elem_of_app elem_of_list_singleton.
        auto. }
      iSplitL "D6 D".
      { iDestruct (diamonds_join with "[$]") as "D".
        iExactEq = "D". iPureIntro. f_equal.
        rewrite app_length /=.
        rew_qz.
        cut (length stack'< size G). lia.
        apply inv_stack_bound in Hinv.
        rewrite app_length /= in Hinv.
        lia. }
      iSplitL "T".
      { iExactEq = "T". iPureIntro. do 2 f_equal.
        rewrite app_length /=. lia. }
      iPureIntro.
      eapply inv_stage_neighbors; eauto.
      unfold add_1 in *.
      apply list_lookup_fmap_inv in Hneighbors_qs.
      destruct Hneighbors_qs as (l1 & [=->->] & ->).
      f_equal. induction l1; simpl; f_equal; auto.
  }

  (** the specification of "iter" has been specialized *)

  wps_weak {[lneighbors; lclosure]} by set_solver.
  (* list_iter returns unit, but wps_binds asks us to prove it for any val, so: *)
  rewrite wps_return_unit_iff.
  (* Fail wps_apply "iter". (* Tactic failure: iPoseProof: "iter" not found *) *)
  iApply (wps_mono with "iter").

  (** we get back list_iter's final invariant *)
  iIntros (?) "(-> & D2 & Hneighbors & I & Pc) Sn Sc".
  iDestruct "I" as "(Hspec & %Htrue & Sg & Ss & Sm & I)".
  iDestruct "I" as (stack marked') "(%Hmarkedcur & Hmarked & D & T & Vs & %Hinv')".

  (** we free the closure *)
  iApply wps_esupd. set_solver. apply (spec_esupd_free lclosure).
  iFrame.
  iIntros "(D3 & Pm2 & Ps2 & _)". simpl.
  iDestruct (mapsfrom_join lmarked with "[$] [$]") as "Pm".
  iDestruct (mapsfrom_join lstack with "[$] [$]") as "Ps".
  rewrite left_id. assert (1 / 2 + 1 / 2 = 1)%Qz as -> by now rewrite Qz_div_2.

  (** we can now apply the induction hypothesis *)
  iDestruct "IH" as "-#IH".
  iSpecialize ("IH" $! (meas - 1)).
  iAssertSpecialize "IH".
  { iPureIntro. destruct Hinv', Hinv. rewrite app_length /= in inv_measure1. lia. }
  iSpecialize ("IH" $! stack marked').
  iAssertSpecialize "IH" with "[D' D2 D3]".
  { do 2 iDestruct (diamonds_join with "[$]") as "?"; now rew_qz. }
  iSpecialize ("IH" with "Ss Sm Sg Pm Ps").
  Fail wps_apply "IH". (* TODO *)
  iApply ("IH" with "Vg [Hlocs_hole Pn Sn Hneighbors]").
  now iApply "Hlocs_hole"; iFrame; auto.
  iFrame; auto.

  Unshelve.
  now rewrite replicate_length; lia.
  now set_solver.
  now rewrite !fmap_length; lia.
  exact tt.
  now rewrite !fmap_length; lia.
Qed.

(*
Remarks:

1) iLöb can't be used, because laters are never removed? -> in fact, we can

2) many times, wps_apply "H" results in:
  Tactic failure: iPoseProof: "H" not found

3) at "let not_empty = vector_size stack", if we don't use wps_bind_nofree, then

  (* TODO: without this mechanism, wps_bind takes a long (infinite?) time *)
  match goal with |- context [tm_if ?a ?b ?c] => remember (tm_if a b c) as t end.
  change t with (id t) in Heqt.
  Opaque id.
  wps_bind; change (id t) with t in Heqt; subst t.
  Transparent id.
  (* solving wps_bind's side obligation more carefully than [set_solver] *)
  {
    simpl.
    repeat
      match goal with
      | |- ∅ ⊆ _ => apply empty_subseteq
      | |- _ ∪ ∅ ⊆ _ => rewrite union_empty_r
      | |- ∅ ∪ _ ⊆ _ => rewrite union_empty_l
      | |- _ ∪ _ ⊆ _ => apply union_least
      | |- locs (subst _ _ _) ⊆ _ => etransitivity; [ now apply locs_subst | ]
      | |- locs_tm (subst _ _ _) ⊆ _ => etransitivity; [ now apply locs_subst | ]
      | |- locs (mk_clo ?s ?a ?c) ⊆ ?r => change (locs_tm (mk_clo s a c) ⊆ r); rewrite (locs_mk_clo s a c)
      | _ => set_solver
      end.
  }
  wps_nofree.
  wps_apply vector_size_amortized_spec.
  simpl.
  rename v0 into nstack.
  iDestruct select (_ ∗ _)%I as "(%E_nstack & V)".
*)
