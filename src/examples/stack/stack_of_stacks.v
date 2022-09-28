From Coq Require Import QArith.Qcanon.
From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From glaneur.fracz Require Import qz smultiset.
From glaneur.language Require Import notation.

From glaneur Require Import more_space_lang wp_all wpc triple.
From glaneur.examples Require Import tactics ref list stack.

(* LATER: Refactor wps_bind to handle arbitrary context. *)

(* Parent & child *)
Module StackSek (P : StackOf) (C : StackOf) : StackOf.

(* We are going to define a stack as a "stack of possibly bounded stacks".

   Given a parent / outer stack implementation P and a child / inner stack
   implementation C, we construct a new stack implementation as a record of:
   + A child stack
   + A parent stack of children.

   Therefore, the final capacity is: *)

Definition capacity :=
  match C.capacity,P.capacity with
  | Some c, Some p => Some (c + c*p)%positive
  | _,_ => None end.

(* The constants empty_cost & cell_cost expose an amortized space complexity:
   The user have to pay a little more at each push to ensure enough credit for the
   creation of a parent cell when needed *)

Definition provision_step : Qz :=
  match C.capacity with
  | None => 0
  | Some c => (C.empty_cost + P.cell_cost) / pos_to_Qp c end.

Definition empty_cost : Qz :=
  2 + C.empty_cost + P.empty_cost.
Definition cell_cost : Qz :=
  C.cell_cost + provision_step.

(* Then the code itself. *)

Definition stack_empty : val :=
  λ: [[]],
    let: "stack" := alloc ^2 in
    let: "front" := C.stack_empty [] in
    let: "tail"  := P.stack_empty [] in
    "stack".[0] <- "front";;
    "stack".[1] <- "tail";;
    "stack".

Definition stack_push : val :=
  λ: [["v","stack"]],
    let: "front" := "stack".[0] in
    let: "is_full" := C.stack_is_full [["front"]] in
    if: "is_full" then
      let: "newfront" := C.stack_empty [] in
      "stack".[0] <- "newfront";;
      let: "tail" := "stack".[1] in
      P.stack_push [["front", "tail"]];;
      C.stack_push [["v", "newfront"]]
    else
      C.stack_push [["v", "front"]].

Definition stack_pop : val :=
  λ: [["stack"]],
    let: "front" := "stack".[0] in
    let: "x" := C.stack_pop [["front"]] in
    let: "front_is_empty" := C.stack_is_empty [["front"]] in
    let: "_" :=
      if: "front_is_empty" then
        let: "tail" := "stack".[1] in
        let: "tail_is_empty" := P.stack_is_empty [["tail"]] in
        if: "tail_is_empty" then val_unit else
          let: "newfront" := P.stack_pop [["tail"]] in
          "stack".[0] <- "newfront"
      else val_unit in
    "x".

Definition stack_is_empty : val :=
  λ: [["stack"]],
    let: "front" := "stack".[0] in
    C.stack_is_empty [["front"]].

Definition stack_is_full : val :=
  λ: [["stack"]],
    let: "front" := "stack".[0] in
    let: "tail" := "stack".[1] in
    let: "fi" := C.stack_is_full [["front"]] in
    let: "ft" := P.stack_is_full [["tail"]] in
    "fi" '* "ft". (* The stack is full iff its front & tail are full *)

Lemma locs_stack_empty : locs stack_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_push : locs stack_push = ∅.
Proof. easy. Qed.
Lemma locs_stack_pop : locs stack_pop = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_empty : locs stack_is_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_full : locs stack_is_full = ∅.
Proof. easy. Qed.

(* ------------------------------------------------------------------------ *)
(* Potential *)

Definition potential (lLF:nat) : Qz :=
  lLF * provision_step.

Lemma potential_zero : potential 0 = 0.
Proof.
  rewrite /potential. rewrite left_absorb //.
Qed.

Lemma potential_full c :
  C.capacity = Some c ->
  potential (Pos.to_nat c) = (C.empty_cost + P.cell_cost)%Qz.
Proof.
  intros Hc.
  rewrite /potential /provision_step Hc.
  assert (nat_to_Qz (Pos.to_nat c) = Qp_to_Qz (pos_to_Qp c)) as ->.
  { rewrite pos_to_qz_through_nat //. }
  rewrite Qz_mul_div_r //.
Qed.

Lemma potential_step n :
  (provision_step + potential n)%Qz = potential (1+n).
Proof.
  rewrite /potential /provision_step.
  destruct C.capacity; simpl; rew_qz; try lia.
  rewrite -Qz_mul_succ_l. rew_qz.
  easy.
Qed.

Module DP := StackDominant(P).

Definition IsFull {A} (L:list A) := Some (length L) = Pos.to_nat <$> C.capacity.

Record StackInv {A} (L LF:list A) (LS:list (list A)) : Prop :=
  make_StackInv {
      stack_items : L = LF ++ concat LS;
      stack_tail_full : Forall IsFull LS;
      stack_tail_nil : LF = nil -> LS = nil;
      stack_front_length :
      match C.capacity with None => True | Some c => length LF <= Pos.to_nat c end;
      stack_tail_length :
      match P.capacity with None => True | Some c => length LS <= Pos.to_nat c end
    }.

Definition StackOf `{!interpGS Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qz * Qp))) (s:loc) : iProp Σ :=
  ∃ (f t:loc) (LF:list (A * (Qz * Qp))) (LT:list (list (A * (Qz * Qp)))),
    ⌜StackInv xs LF LT⌝ ∗ ♢ (potential (length LF)) ∗
    s ↦ BBlock [val_loc f;val_loc t] ∗ Stackable f 1%Qp ∗ f ↤ {[+ s +]} ∗
      Stackable t 1%Qp ∗ t ↤ {[+ s +]} ∗
      C.StackOf R LF f ∗
      DP.StackDominantOf (fun xs => post (C.StackOf R xs)) 1%Qp LT t.

Ltac destruct_stack Hs :=
  iDestruct Hs as
    "[%f [%t [%LF [%LT (%Hinv & Hdiams & ? & ? & ? & ? & ? & Hf & Ht)]]]]".

Lemma stack_is_empty_spec `{interpGS Σ} A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun n => ⌜n ≠ 0 <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  pose proof C.locs_stack_is_empty.
  iStepsS.
  wps_bind. iStepsS.
  wps_context f.
  wps_apply C.stack_is_empty_spec as (n) "[%Hn ?] ?".
  iSplitR.
  { destruct Hinv as [? ? Ht]. iPureIntro. subst.
    split; intros He.
    { apply Hn in He. rewrite He Ht //. }
    { apply app_nil in He; destruct He. intuition. } }
  { iExists _,_,_,_. by iFrame. }
Qed.

Lemma length_concat A c (xs:list (list A)):
  Forall (fun x => length x = c) xs ->
  length (concat xs) = c * length xs.
Proof.
  induction xs; simpl; try lia.
  intros E. apply Forall_cons_1 in E. destruct E.
  rewrite app_length IHxs //. lia.
Qed.

Lemma length_concat_full A c (xs:list (list A)):
  C.capacity = Some c ->
  Forall IsFull xs ->
  length (concat xs) = (Pos.to_nat c * length xs).
Proof.
  intros Hc ?.
  eapply length_concat; eauto.
  eapply Forall_impl; eauto.
  unfold IsFull. rewrite Hc. intros ? E. injection E. easy.
Qed.

Lemma mult_neq_zero (n m : nat) :
  n * m ≠ 0 <-> n ≠ 0 /\ m ≠ 0.
Proof. lia. Qed.

Lemma stack_is_full_correct A nf nt (xs LF : list A) LT :
  StackInv xs LF LT ->
  nf ≠ 0 ↔ ¬ size_lt (length LF) C.capacity ->
  nt ≠ 0 ↔ ¬ size_lt (length LT) P.capacity ->
  nf * nt ≠ 0 ↔ ¬ size_lt (length xs) capacity.
Proof.
  intros [-> ? Hf Ht] Hnf Hnt.
  unfold size_lt in *.
  rewrite /capacity.
  destruct C.capacity eqn:Hc.
  2:{ split; try easy. intros E.
      apply mult_neq_zero in E. destruct E. now apply Hnf. }
  destruct P.capacity.
  2:{ split; try easy. intros E.
      apply mult_neq_zero in E. destruct E. now apply Hnt. }
  rewrite app_length. erewrite length_concat_full; eauto.
  nia.
Qed.

Lemma stack_is_full_spec `{interpGS Σ} A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun n => ⌜n ≠ 0 <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs".
  pose proof C.locs_stack_is_full.
  pose proof P.locs_stack_is_full.

  wps_call. destruct_stack "Hs".
  wps_context t.
  wps_bind. wps_load.
  wps_context f.
  wps_bind. wps_load. simpl.
  wps_bind.
  wps_apply C.stack_is_full_spec as "(%Hnf & ?)".
  wps_bind.
  wps_apply DP.stack_is_full_spec_dominant as "(%Hnt & ?)".
  wps_bin_op. iIntros.
  iSplitR.
  { eauto using stack_is_full_correct. }
  iExists f,t,_,_. by iFrame.
Qed.

Lemma StackInv_empty A :
  @StackInv A nil nil nil.
Proof.
  constructor; try easy.
  unfold size_lt.
  destruct C.capacity; simpl in *; lia.
  destruct P.capacity; simpl in *; lia.
Qed.

Lemma stack_empty_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ Stackable s 1%Qp ∗ s ↤ ∅).
Proof.
  iIntros. rewrite /empty_cost.
  pose proof C.locs_stack_empty.
  pose proof P.locs_stack_empty.
  wps_call.
  wps_bind.
  wps_alloc s as "(? & ? & ? & ?)".
  { rewrite -assoc. apply Qz_le_add_l. }
  wps_context s.
  wps_bind.

  assert ((2 + C.empty_cost + P.empty_cost - 2)%Qz = (C.empty_cost + P.empty_cost)%Qz ) as ->.
  { rewrite -assoc Qz_add_sub //. }
  iDestruct (diamonds_split with "[$]") as "(Hdc & Hdp)".
  wps_apply (C.stack_empty_spec _ R) as (c) "(? & ? & ?)".
  wps_context c.
  wps_bind.
  wps_apply (DP.stack_empty_dominant_spec _(λ xs : list (A * (Qz * Qp)), post (C.StackOf R xs)))
    as (p) "(? & ? & ?)".
  wps_bind. wps_store.
  rewrite left_id. iIntros.
  wps_bind. wps_store.
  iApply @wps_bupd. iMod diamonds_zero as "?". iModIntro.
  wps_val.
  rewrite left_id. iIntros.
  iFrame.
  iExists c,p,_,_. iFrame.
  rewrite potential_zero. iFrame.
  eauto using StackInv_empty.
Qed.

Lemma StackInv_push A x (xs LF:list A) LT :
  size_lt (length LF) C.capacity ->
  StackInv xs LF LT ->
  StackInv (x::xs) (x::LF) LT.
Proof.
  intros ? [Hi ? ? ?].
  constructor; try easy.
  rewrite Hi //.
Qed.

Lemma StackInv_push' A x (xs LF:list A) LT :
  size_lt (length LT) P.capacity ->
  IsFull LF ->
  StackInv xs LF LT ->
  StackInv (x::xs) [x] (LF::LT).
Proof.
  intros ? ? [Hi ? ? ?].
  constructor; try easy.
  { rewrite Hi //. }
  { now constructor. }
  { destruct C.capacity; simpl in *; lia. }
Qed.

Lemma stack_push_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) s qp qz v x xs :
  size_lt (length xs) capacity ->
  qz ≠ 0%Qz ->
  CODE (stack_push [[v, s]])
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅)
  POST (fun tt => StackOf R ((x,(qz,qp))::xs) s).
Proof.
  iIntros (Hiu ?) "(? & Hs & ? & ? & ?)".
  pose proof C.locs_stack_is_full.
  pose proof C.locs_stack_empty.
  pose proof C.locs_stack_push.
  pose proof P.locs_stack_push.
  wps_call.
  destruct_stack "Hs".

  wps_bind. wps_load. iIntros.
  wps_bind.
  wps_apply C.stack_is_full_spec as (n) "[%Hn Hf]". iIntros.

  wps_if.

  case_decide as n_eq.
  (* The front is full, we need to push it. *)
  { apply Hn in n_eq. clear Hn.
    unfold size_lt in *.
    destruct C.capacity as [c|] eqn:Hc; try easy.
    assert (length LF = Pos.to_nat c) as Hlf.
    { destruct Hinv as [_ _ _ Hlf]. rewrite Hc in Hlf. simpl in *. lia. }
    rewrite Hlf potential_full //.

    wps_bind.
    iDestruct (diamonds_split with "[$]") as "[Hd1  Hd2]".
    wps_apply (C.stack_empty_spec _ R) as (nf) "(? & ? & ? )".
    iIntros.
    wps_context nf.
    wps_bind.
    wps_store. iIntros.
    wps_bind. wps_load. simpl. iIntros "Hcf ?".
    wps_bind.

    assert (size_lt (length LT) P.capacity).
    { unfold size_lt.
      rewrite /capacity Hc in Hiu.
      destruct Hinv.
      destruct P.capacity; try easy. subst.
      rewrite app_length (length_concat_full _ c) // in Hiu.
      nia. }

    rewrite left_id. assert ({[-s-]} ⊎ {[+ s +]} ≡ ∅) as -> by smultiset_solver.

    wps_context t.
    wps_apply DP.stack_push_dominant_spec; eauto.
    rewrite post_loc. iFrame. iIntros.

    rewrite /cell_cost.
    iDestruct (diamonds_split with "[$]") as "(? & ?)".

    wps_apply C.stack_push_spec.
    { unfold size_lt. rewrite Hc. simpl in *. lia. }
    { eauto. }

    iIntros.
    iExists _,_,_,_. iFrame.
    iSplitR.
    { iPureIntro. apply StackInv_push'; try easy. unfold IsFull.
      rewrite Hc Hlf. easy. }
    { rewrite /potential Qz_mul_1_l.
      conclude_diamonds. } }
  { rewrite /cell_cost.
    iDestruct (diamonds_split with "[$]") as "(? & ?)".

    assert (size_lt (length LF) C.capacity).
    { unfold size_lt in *. destruct C.capacity as [c|]; try easy.
      destruct (decide (length LF < Pos.to_nat c)); try easy.
      exfalso. intuition. }
    wps_context f.
    wps_apply C.stack_push_spec; try easy.
    iIntros.

    iExists _,_,_,_. iFrame.
    iSplitR.
    { eauto using StackInv_push. }
    { conclude_diamonds. apply potential_step. } }
Qed.

Module MC := MoreStackOf(C).

Lemma StackInv_pop A x (xs LF:list A) LT :
  (LF = [] -> LT = []) ->
  StackInv (x::xs) (x::LF) LT ->
  StackInv xs LF LT.
Proof.
  intros ? [Hi ? ? Hf].
  simpl in *. injection Hi. intros. subst.
  constructor; try easy.
  destruct C.capacity; simpl in *; lia.
Qed.

Lemma StackInv_pop' A x (hLT:list A) tLT :
  StackInv (x :: hLT ++ concat tLT) [x] (hLT :: tLT) ->
  StackInv (hLT ++ concat tLT) hLT tLT.
Proof.
  intros [? Hf ? ?].
  apply Forall_cons_1 in Hf. destruct Hf as (Hh & ?).
  unfold IsFull in *.
  constructor; try easy.
  { intros ->.
    destruct C.capacity as [c|]; simpl in *; try easy.
    injection Hh. intros ?. pose proof (Pos2Nat.is_pos c). lia. }
  { destruct C.capacity; try easy. injection Hh. lia. }
  { destruct P.capacity; simpl in *; lia. }
Qed.

Lemma stack_pop_spec `{!interpGS Σ} A (R:A -> val -> iProp Σ) s qp qz x xs :
  CODE (stack_pop [[s]])
  SOUV {[s]}
  PRE  (StackOf R ((x,(qz,qp))::xs) s)
  POST (fun v => R x v ∗ vStackable v qp ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).
Proof.
  iIntros "Hs".
  pose proof C.locs_stack_is_empty.
  pose proof P.locs_stack_is_empty.
  pose proof P.locs_stack_pop.
  pose proof C.locs_stack_pop.
  wps_call.

  destruct_stack "Hs".
  wps_bind. wps_load.
  wps_bind.

  assert (LF ≠ nil).
  { destruct Hinv as [HE _ Ht _].
    intros ->. rewrite Ht in HE; easy. }

  wps_apply MC.stack_pop_spec' as (v) "[%x' [%LF' [%qz' [%qp' (%HE' & ? & ? & ? & Hf & Dpop)]]]]".
  { eauto. }
  iIntros "Hcf".

  generalize Hinv. intros [HE Hf Ht ?].
  rewrite HE' in HE. simpl in HE. injection HE. intros.
  subst x' qz' qp'.

  rewrite /cell_cost.
  assert (potential (length LF) =
            (provision_step + potential (length LF'))%Qz ) as ->.
  { rewrite /potential HE'. simpl.
    assert (nat_to_Qz (S (length LF')) = 1 + nat_to_Qz (length LF'))%Qz as ->.
    { rew_qz. lia. }
    rewrite Qz_mul_succ_l //. }
  iDestruct (diamonds_split with "[$]") as "(Dpro & Drest)".

  iDestruct (diamonds_join with "[Dpop Dpro]") as "?". iFrame "Dpop". iFrame.

  wps_context v.
  wps_bind.
  wps_context f.
  wps_apply C.stack_is_empty_spec as (n) "[%Hn Hf] ?".

  wps_bind.
  wps_if.

  case_decide as Hnz; last first.
  (* The front chunk is not empty *)
  { do 6 iStepS. iIntros. iFrame.
    iExists _,_,_,_. iFrame.
    iPureIntro. subst.
    eapply StackInv_pop; eauto.
    intros ->. exfalso. destruct Hn as (_&Hn). now apply Hn. }

  (* The front chunk is now empty, we try to pop in the tail. *)
  { assert (LF' = nil) by (now apply Hn). subst LF'. clear Hn Hnz n.
    wps_bind. wps_load.
    wps_bind.
    wps_apply DP.stack_is_empty_spec_dominant as (nt) "[%Hnt ?]". iIntros.

    wps_if.
    case_decide as Hntz.

    (* The tail is empty, the whole stack is now empty. *)
    { do 6 iStepS. iIntros. iFrame.
      rewrite /cell_cost. iFrame.
      iExists f,t,_,_. iFrame.
      iPureIntro.
      eapply StackInv_pop; eauto.
      intros. apply Hnt. eauto. }

    (* The tail is not empty, we pop a chunk ! *)
    { wps_bind.
      wps_context t.
      wps_apply DP.stack_pop_dominant_spec' as (vnf) "[%y [%ys [%Heys (Hpost & ? & ? & ? & ?)]]]".
      { intros ->. destruct Hnt as (_&Hnt). now apply Hnt. }
      iDestruct "Hpost" as "[%nf [%Enf ?]]". subst vnf. iIntros.
      rew_enc. wps_store. iIntros.

      rewrite left_id.
      rewrite left_id. assert (({[-s-]} ⊎ {[+ s +]}) ≡ ∅) as -> by smultiset_solver.

      iApply @wps_esupd.
      { set_solver. }
      { apply @C.stack_free. }
      iFrame.

      iIntros "(Dof & ? & ?)".
      do 6 iStepS. iIntros. iFrame.
      iExists nf,t,_,_. iFrame.
      do 2 iDestruct (diamonds_join with "[$]") as "?".
      iSplitR.
      { subst. simpl in *. eauto using StackInv_pop'. }
      { conclude_diamonds.
        subst.

        rewrite potential_zero right_id right_absorb right_id.

        apply Forall_cons in Hf.
        destruct Hf as (Hy & _).
        unfold IsFull in *.
        destruct C.capacity eqn:E; simpl in *; try easy. injection Hy.
        intros ->.
        rewrite potential_full //. } } }
Qed.

Lemma free_soup_children `{!interpGS Σ} A (R:A -> val -> iProp Σ) LT vs c :
  C.capacity = Some c ->
  Forall IsFull LT ->
  (([∗ list] x;v ∈ LT;vs, v ↤? ∅ ∗ vStackable v 1%Qp ∗ post (C.StackOf R x) v) =#=∗
     ♢((C.empty_cost+C.cell_cost*(Pos.to_nat c)) * length LT) ∗ ∃ vs', soup R ∅ (concat LT) vs')%I.
Proof.
  iIntros (Hc Hf).
  iInduction LT as [|x LT] "IH" forall (vs); iIntros "?"; iIntros (? ? ?) "Hi".
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hvs".
    subst. simpl. rewrite right_absorb.
    iMod diamonds_zero. iFrame. iExists nil. iApply soup_empty. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%v' [%vs' (%Hvs' & (Hml & Hcl & Hpost) & Hvs')]]".
    subst.
    apply Forall_cons_1 in Hf. destruct Hf as (Hx&?).
    iDestruct "Hpost" as "[%l (%Hl & Hl)]". subst. rew_enc. simpl.

    iMod ("IH" with "[%] [$] [Hi]") as "(Hr & Dvs' & Hs)".
    { eauto. }
    { iFrame. }
    iClear "IH".

    iMod (C.stack_free _ R l x with "[$] [$]") as "(? & ? & ? & Hs')"; try iFrame.
    iModIntro.
    iDestruct (diamonds_join with "[$]") as "?".
    iDestruct (diamonds_eq with "[$]") as "?"; last iFrame.
    { rewrite /IsFull Hc in Hx. injection Hx. intros ->.
      rewrite (comm Qz_mul _  (length LT)) (comm Qz_mul _ (S (length LT))).
      rewrite -Qz_mul_succ_l. f_equal.
      now rew_qz. }
    iApply soup_app_exists. iFrame. }
Qed.

Lemma StackInv_capa_None A xs LF LT :
  C.capacity = None ->
  @StackInv A xs LF LT ->
  LT = nil /\ xs = LF.
Proof.
  intros Hc [-> Ht _ _ _].
  destruct LT; simpl.
  { rewrite right_id //. }
  { exfalso. apply Forall_cons_1 in Ht. destruct Ht as (Hf & ?).
    rewrite /IsFull Hc in Hf. inversion Hf. }
Qed.

Lemma StackInv_inv_length A xs LF LT c :
  C.capacity = Some c ->
  @StackInv A xs LF LT ->
  length xs = length LF + Pos.to_nat c * length LT.
Proof.
  intros Hc [-> Ht _ _ _].
  rewrite app_length (length_concat_full _ c) //.
Qed.

Lemma stack_free `{!interpGS Σ} A (R:A -> val -> iProp Σ) s xs :
  Stackable s 1%Qp ∗ s ↤ ∅ ∗ StackOf R xs s =#=∗
  ♢(empty_cost+cell_cost*length xs) ∗ †s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(? & ? & Hs)". iIntros.
  destruct_stack "Hs".

  iMod (@logical_free _ _ _ _ s with "[$] [$]") as "(? & Dblock & #Hs)"; try easy.

  iMod (mapsfrom_cleanup _ f with "[$] [$]") as "(? & ?)".
  iMod (mapsfrom_cleanup _ t with "[$] [$]") as "(? & ?)".
  assert (({[+ s +]} ⊎ {[-s-]}) ≡ ∅) as -> by smultiset_solver.

  iMod (C.stack_free _ R f with "[$] [$]") as "(? & Df & #Hf & ? )"; try easy.
  iMod (DP.stack_dominant_free _ _ 1%Qp LT t  with "[$] [$]") as "(? & Dt & #Ht & [%vc Hchildren] )"; try easy.

  iFrame "Hs".

  destruct C.capacity as [c|] eqn:Hc.
  { iMod (free_soup_children with "[$] [$]") as "(? & Dc & ?)". 1,2:(destruct Hinv; now eauto).
    iFrame. iModIntro.
    iSplitL "Hdiams Dblock Df Dt Dc"; last first.
    { destruct Hinv as [-> _ _ _ _]. iApply soup_app_exists. iFrame. }
    rewrite /empty_cost.
    do 2 iDestruct (diamonds_split with "[$]") as "[? ?]".
    rewrite /potential.
    rewrite /cell_cost.
    eapply StackInv_inv_length in Hinv; eauto. rewrite Hinv.
    rewrite nat_to_Qz_add Qz_mul_add_distr_l.
    do 2 rewrite Qz_mul_add_distr_r.
    rewrite (comm _ provision_step).
    repeat rewrite diamond_split_iff. iFrame.
    rewrite -diamond_split_iff.
    iDestruct (diamonds_join with "[$]") as "?".

    do 2 rewrite -Qz_mul_add_distr_r.
    rewrite nat_to_Qz_mul. rewrite (assoc Qz_mul).
    conclude_diamonds.
    f_equal.

    rewrite /provision_step Hc pos_to_qz_through_nat.
    rewrite Qz_mul_add_distr_r Qz_mul_div_l.
    rewrite (comm Qz_add P.cell_cost) assoc. f_equal.
    rewrite (comm Qz_add) //. }
  { apply StackInv_capa_None in Hinv; last easy.
    destruct Hinv. subst.
    iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hvs". subst.
    iFrame.
    rewrite /empty_cost.
    do 2 iDestruct (diamonds_split with "[$]") as "[? ?]".
    repeat rewrite diamond_split_iff. iFrame.
    do 2 iDestruct (diamonds_join with "[$]") as "?".
    conclude_diamonds.
    simpl. rewrite right_absorb right_id.
    rewrite /cell_cost /potential /provision_step Hc right_id right_absorb right_id //. }
Qed.
End StackSek.
