From stdpp Require Import decidable binders gmultiset.
From iris Require Import proofmode.proofmode algebra.gmap.
From spacelambda Require Import language.notation more_space_lang wp_all triple.
From spacelambda.examples Require Import tactics utils diaframe.

(** TODO move *)
Lemma wp_enc_return_unit_iff `{!interpGS Σ} `{Enc A} b t (Q : iProp Σ) :
  wp_enc b t (λ _ : (), Q) ⊣⊢ wp_enc b t (λ r : val, ⌜r = ()%V⌝ ∗ Q).
Proof.
  rewrite !wp_enc_eq /post.
  apply bi.equiv_entails; split;
    iIntros "w"; iApply (wp_mono with "w");
    iIntros (v) "w";
    iDestruct "w" as ([]) "(-> & q)";
    iExists val_unit || iExists tt;
    auto.
Qed.

Lemma wpc_eq `{!interpGS Σ} `{Enc A} r t Q :
  wpc r t Q = (∀ k : lctx, ⌜r ⊆ dom k⌝ -∗ Stackables k -∗ wp_enc true t (λ a : A, Stackables k ∗ Q a))%I.
Proof.
  reflexivity.
Qed.

Lemma wps_return_unit_iff `{!interpGS Σ} `{Enc A} X t (Q : iProp Σ) :
  wps X t (λ _ : (), Q) ⊣⊢ wps X t (λ r : val, ⌜r = ()%V⌝ ∗ Q).
Proof.
  rewrite !wps_eq.
  destruct X. 2: now apply wp_enc_return_unit_iff.
  rewrite !wpc_eq.
  apply bi.equiv_entails; split.
  - iIntros "w" (a) "%Ha Sa".
    iSpecialize ("w" $! a Ha with "Sa").
    iApply (wp_enc_mono with "[-]").
    + iApply wp_enc_return_unit_iff. iApply "w".
    + iIntros (v) "($ & $ & $)".
  - iIntros "w" (a) "%Ha Sa".
    iSpecialize ("w" $! a Ha with "Sa").
    iApply wp_enc_return_unit_iff.
    iApply (wp_enc_mono with "[-]").
    + iApply "w".
    + iIntros (v) "($ & $ & $)".
Qed.

Lemma wps_unit_val `{!interpGS Σ} `{Enc A} X t (Q : iProp Σ) :
  wps X t (λ _ : (), Q) -∗ wps X t (λ _ : val, Q).
Proof.
  iIntros "w".
  iApply (wps_mono with "[w]").
  iApply (wps_return_unit_iff with "w").
  iIntros (v) "(_ & $)".
Qed.

Definition Vector `{!interpGS Σ} (vs : list (val * Qp)) (l : loc) (capacity : nat) : iProp Σ :=
  ∃ (l' : loc),
    ⌜ length vs <= capacity /\ 0 < capacity ⌝
    ∗ l ↦ BBlock [ #l'; ^capacity; ^(length vs) ]
    ∗ Stackable l' 1%Qp
    ∗ l' ↦ BBlock (vs.*1 ++ replicate (capacity - length vs) ())
    ∗ l' ↤ {[+ l +]}
    ∗ ([∗ list] vq ∈ vs, let '(v, q) := vq in vStackable v q ∗ v ↤?{q} {[+ l' +]}).

Definition vector_create : val :=
  λ: [[]],
    let: "c" := alloc 3 in
    "c".[1] <- ^1 ;;
    "c".[2] <- ^0 ;;
    let: "v" := alloc ^1 in
    "c".[0] <- "v" ;;
    "c".

Lemma vector_create_spec `{!interpGS Σ} :
  CODE (vector_create [[]])
  PRE (♢ 4)
  POST (fun (l:loc) => Vector [] l 1 ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  iIntros "?".
  wps_call.
  wps_bind. wps_alloc l as "(? & ? & ? & ?)".
  wps_bind. (* Fail wps_store. *) do 7 iStepS.
  wps_bind. (* Fail wps_store. *) do 7 iStepS.
  wps_bind. wps_alloc l'. do 1 iStepS.
  wps_bind. wps_store. do 3 iStepS.
  iFrame.

  rew_qz.
  iExists l'. rewrite /= left_id. iFrame.
  iPureIntro; lia.
Qed.

Definition vector_size : val :=
  λ: [["p"]],
    "p".[2].

Lemma vector_size_spec `{!interpGS Σ} vs l cap :
  CODEFF (vector_size [[#l]])
  PRE (Vector vs l cap)
  POST (fun r : nat => ⌜r = length vs⌝ ∗ Vector vs l cap).
Proof.
  iIntros "V".
  iDestruct "V" as (l') "(% & ?)".
  repeat iStepS.
Qed.

Parameter time_credit : forall `{!interpGS Σ}, nat -> iProp Σ.
Notation "$ n" := (time_credit n)%I%Qz (at level 20) : bi_scope.

Parameter time_step_spec : forall `{!interpGS Σ}, forall n m X,
    triple X
      ($ (n + m))
      ("time_step" [[^n]])%T
      (λ _ : unit, ($ m))%I.

Definition array_copy : val :=
  μ: "self", [["dst", "src", "i", "n"]],
    let: "neq" := "n" '- "i" in
    if: "neq" then
      "time_step" [[^1]];;
      let: "x" := "src".["i"] in
      "dst".["i"] <- "x";;
      let: "i" := "i" '+ ^1 in
      "self" [["dst", "src", "i", "n"]]
    else
      ()%V.

Lemma Qp_not_zero (q : Qp) : (q : Qz) ≠ 0%Qz.
Proof.
  assert (0 < Qp_to_Qz q)%Qz as P by now destruct q.
  intros E; rewrite E in P. revert P.
  now eapply irreflexivity, StrictOrder_Irreflexive.
Qed.

Lemma array_copy_spec `{!interpGS Σ} dst src (src1 src2 src3 dst1 dst3 : list (val * Qp)) (time : nat) :
  length src1 = length dst1 ->
  CODE (array_copy [[#dst, #src, ^(length src1), ^(length src1 + length src2)]])
  SOUV {[dst; src]}
  PRE ($ (length src2 + time)
     ∗ src ↦ BBlock (src1.*1 ++ src2.*1 ++ src3.*1)
     ∗ dst ↦ BBlock (dst1.*1 ++ replicate (length src2) () ++ dst3.*1)
     ∗ [∗ list] vq ∈ src2, let '(v, q) := vq in vStackable v q ∗ v ↤?{q} {[+ src +]})
  POST (fun _ : () =>
       $ time
     ∗ src ↦ BBlock (src1.*1 ++ src2.*1 ++ src3.*1)
     ∗ dst ↦ BBlock (dst1.*1 ++ src2.*1 ++ dst3.*1)
     ∗ [∗ list] vq ∈ src2, let '(v, q) := vq in vStackable v q ∗ v ↤?{q} {[+ src; dst +]}).
Proof.
  replace (length dst1) with (length dst1.*1) by rewrite map_length //.
  replace (length src1) with (length src1.*1) by rewrite map_length //.
  replace (length src2) with (length src2.*1) by rewrite map_length //.
  iIntros (E1).
  iInduction (src2) as [ | (v, q) src2 ] "IH" forall (src1 src3 dst1 dst3 E1);
    iIntros "(? & ? & ?)".
  - wps_call.
    (* we establish that the condition is false *)
    wps_bind. wps_val.
    replace (_ - _) with 0 by lia.
    wps_if.
    wps_val.
    iFrame.

  - wps_call.
    iDestruct select (_ ∗ _)%I  as "(? & ?)".
    (* we establish that the condition is true *)
    wps_bind. wps_val.
    wps_if. destruct (decide _) as [D|D]. 2:lia.

    (* time step *)
    wps_bind.
    wps_apply time_step_spec.

    (* loads v *)
    wps_bind.
    unshelve wps_load.
    { rewrite app_length /= app_length map_length. lia. }
    rewrite list_lookup_total_middle //.
    (* stores v then unit *)
    wps_bind. unshelve wps_store.
    { rewrite app_length /= !map_length /= app_length /= in E1, D |- *; lia. }
    { intro; apply Qp_not_zero. }

    (* the store introduced some extra vmapsfroms, one of them being for unit *)
    rewrite !list_lookup_total_middle /= //. iClear select True%I.

    (* i+1 *)
    wps_bind. wps_val.

    (* massaging to match the I.H. *)
    replace (length src1.*1 + 1) with (length (src1.*1 ++ [v])) by now rewrite app_length map_length /=; lia.
    replace (length src1.*1 + _) with (length (src1.*1 ++ [v]) + length (src2.*1)) by now rewrite app_length !map_length /=; lia.
    rewrite insert_app_r_alt /=. 2: rewrite fmap_length in E1, D |- *; lia. rewrite !map_length in E1 |- *. replace (_ - _) with O by lia. simpl.
    rewrite (cons_middle _ dst1.*1) (app_assoc dst1.*1).
    rewrite (cons_middle _ src1.*1) (app_assoc src1.*1).
    assert (length (src1.*1 ++ [v]) = length (dst1.*1 ++ [v])) by now rewrite !app_length !map_length /=; lia.
    replace (src1.*1 ++ [v]) with (src1 ++ [(v, q)]).*1 by rewrite fmap_app //.
    replace (dst1.*1 ++ [v]) with (dst1 ++ [(v, q)]).*1 by rewrite fmap_app //.

    (* we can finally apply the induction hypothesis -- only thing to be framed is v's mapsfrom *)
    wps_apply "IH"; auto.
    rewrite !map_length !app_length E1 //.
    rewrite !fmap_app -!app_assoc.
    iFrame.
Unshelve. apply tt.
Qed.


Definition vector_resize : val :=
  λ: [["p", "newcap"]],
    let: "size" := "p".[2] in
    let: "oldv" := "p".[0] in
    "time_step" [["newcap"]];;
    let: "newv" := alloc "newcap" in
    array_copy [["newv", "oldv", ^0, "size"]];;
    "p".[0] <- "newv";;
    "p".[1] <- "newcap".

Lemma vmapsfroms_cleanup_supd `{!interpGS Σ} b vs l' q ls L:
  ([∗ list] v ∈ vs, v ↤?{q} ls) ∗ †l' =[b | L]=∗
  ([∗ list] v ∈ vs, v ↤?{q} (ls ⊎ {[-l'-]})).
Proof.
  iIntros "(Pvs & #dl)". iIntros (? ? ?) "Hi".
  iInduction vs as [ | v vs ] "IH". by auto.
  iDestruct "Pvs" as "(Pv & Pvs)".
  iDestruct (vmapsfrom_cleanup with "[$Pv $dl] Hi") as ">(Hi & $ & _)".
  iDestruct ("IH" with "Pvs Hi") as ">($ & $)".
  auto.
Qed.

Lemma vmapsfroms_val_Qp_cleanup_supd `{!interpGS Σ} b vs l' ls L:
  ([∗ list] vq ∈ vs, let '(v,q) := vq in vStackable v q ∗ v ↤?{q} ls) ∗ †l' =[b | L]=∗
  ([∗ list] vq ∈ vs, let '(v,q) := vq in vStackable v q ∗ v ↤?{q} (ls ⊎ {[-l'-]})).
Proof.
  iIntros "(Pvs & #dl)". iIntros (? ? ?) "Hi".
  iInduction vs as [ | (v, q) vs ] "IH". by auto.
  simpl big_opL.
  iDestruct "Pvs" as "((Sv & Pv) & Pvs)".
  iDestruct (vmapsfrom_cleanup with "[$Pv $dl] Hi") as ">(Hi & $ & _)".
  iDestruct ("IH" with "Pvs Hi") as ">($ & $)".
  auto.
Qed.

Lemma vector_resize_spec `{!interpGS Σ} vs (oldcap newcap : nat) l time :
  0 < newcap ->
  length vs <= newcap ->
  CODE (vector_resize [[#l, ^newcap]])
  SOUV {[l]}
  PRE (Vector vs l oldcap ∗ ♢newcap ∗ $ (newcap + (length vs + time)))
  POST (fun _ : () => Vector vs l newcap ∗ ♢oldcap ∗ $ time).
Proof.
  iIntros (Pnewcap Hnewcap) "(V & ? & ?)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & Hl & Sl' & Hl' & pl' & PS)".
  wps_call.
  wps_bind. wps_load.
  wps_bind. wps_load.
  wps_bind. wps_apply time_step_spec. iIntros.
  wps_bind. wps_alloc l'' as  "(dia & Hl'' & pl'' & Sl'')".
  iIntros "Sl'".
  iRename select ($ _)%I into "T".
  iPoseProof
    (array_copy_spec l'' l' nil vs
       (replicate (oldcap - length vs) (()%V, 1%Qp)) nil
       (replicate (newcap - length vs) (()%V, 1%Qp)) time
      with "[Hl' PS Hl'' T]") as "A"; auto;
  [ rewrite !fmap_replicate -replicate_plus;
    replace (length vs + (newcap - length vs)) with newcap by lia;
    iFrame; auto | ].

  wps_bind.
  iApply (wps_context_singleton l'). iFrame.
  iApply (@wps_weak _ _ _ _  {[l''; l']}). now multiset_solver.
  iApply wps_unit_val.
  iApply (wps_mono with "A").
  iIntros (_) "(?&?&?&Pvs) ?".
  iIntros "?".
  wps_bind. wps_store.
  assert ({[-l-]} ⊎ {[+l+]} ≡ ∅) as -> by smultiset_solver.
  rew_qz. simpl plus.
  iApply (wps_confront_Stackable l' with "[$]"). iIntros "% ?".
  wps_free l' as "(? & #dl')".
  rewrite wps_return_unit_iff.
  iApply (wps_esupd _ _ _ _ (vmapsfroms_val_Qp_cleanup_supd true _ l' _ _)).
  iSplitL "Pvs". by iFrame. iIntros "Pvs".
  rewrite -wps_return_unit_iff.
  do 5 iStepS.
  rewrite left_id.
  rewrite /= app_length !fmap_replicate replicate_length map_length.
  replace (length vs + (oldcap - length vs)) with oldcap by lia.
  iFrame.
  iExists _; iFrame.
  iSplitR. iPureIntro; lia.
  rewrite big_sepL_proper. iFrame.
  intros ? (?, ?) ?.
  assert (({[+ l'; l'' +]} ⊎ {[-l'-]} : smultiset _)
            ≡ {[+ l'' +]}) as -> by smultiset_solver.
  auto.
  Unshelve.
  set_solver.
Qed.

Definition vector_push : val :=
  λ: [["p", "x"]],
    let: "cap" := "p".[1] in
    let: "size" := "p".[2] in
    let: "diff" := "cap" '- "size" in
    "time_step" [[^1]];;
    (if: "diff" then ()%V else
       let: "newcap" := "cap" '* ^2 in
       vector_resize [["p", "newcap"]]
    )%V;;
    let: "v" := "p".[0] in
    "v".["size"] <- "x";;
    let: "size" := "size" '+ ^1 in
    "p".[2] <- "size".

Lemma vector_push_spec_no_resize `{!interpGS Σ} vs l v (q : Qp) cap time :
  length vs < cap ->
  CODE (vector_push [[#l, v]])
  SOUV {[l]}
  PRE (vStackable v q ∗ v ↤?{q} ∅ ∗ Vector vs l cap ∗ $ (S time))
  POST (fun _ : () => Vector (vs ++ [(v, q)]) l cap ∗ $ time).
Proof.
  iIntros (Hvs) "(Sv & pv & V & T)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & Hl & Sl' & Hl' & pl' & PS)".
  wps_nofree.
  wps_call.
  wps_bind. wps_load.
  wps_bind. wps_load.
  wps_bind. wps_val.
  wps_bind. wps_apply time_step_spec.
  wps_bind. wps_if. destruct (decide _) as [d|e]. 2:lia.
  wps_val.
  wps_bind. wps_load.
  wps_bind. unshelve wps_store; [ .. | ].
  now rewrite app_length replicate_length map_length; lia.
  now intro; apply Qp_not_zero.
  wps_bind. wps_val; [ .. | ].
  do 5 iStepS.
  iFrame.
  iExists l'.
  rewrite app_length /=.
  iSplitR. now iPureIntro; lia.
  iFrame.
  rewrite insert_app_r_alt map_length /= // Nat.sub_diag.
  replace (cap - length vs) with (1 + (cap - (length vs + 1))) by lia.
  rewrite fmap_app -app_assoc /= left_id.
  iFrame.
Qed.

Lemma vector_push_spec_resize `{!interpGS Σ} vs l v (q : Qp) cap time :
  length vs = cap ->
  CODE (vector_push [[#l, v]])
  SOUV {[l]}
  PRE (vStackable v q ∗ v ↤?{q} ∅ ∗ Vector vs l cap ∗ ♢(length vs * 2) ∗ $ (S (length vs * 3 + time)))
  POST (fun _ : () => Vector (vs ++ [(v, q)]) l (cap * 2) ∗ ♢(length vs) ∗ $ time).
Proof.
  iIntros (Hvs) "(Sv & pv & V & dia & T)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & Hl & Sl' & Hl' & pl' & PS)".
  wps_call.
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. wps_val; [ .. | iIntros "Sv"].
  wps_bind. wps_apply time_step_spec. iIntros "Sv".
  wps_bind. wps_if. destruct (decide _) as [d|e]. lia.
  wps_bind. wps_val.
  assert (length vs <= length vs * 2) as A by lia.
  replace (length vs * 3 + time)%nat with (length vs * 2 + (length vs + time))%nat by lia.
  wps_apply vector_resize_spec. lia. eassumption.
  rew_qz. iFrame.
  iSplitR "pv".
  + iExists l'. iFrame.
    iSplitR; auto.
  + iIntros (_) "(V&?&T) ?".
    iDestruct "V" as (l'') "((%Hlen' & %Hcap') & Hl & Sl' & Hl' & pl' & PS)".
    wps_bind. wps_load. iIntros "?".
    wps_bind. unshelve wps_store.
    { rewrite app_length replicate_length map_length. lia. }
    { intro; apply Qp_not_zero. }
    wps_bind. wps_val.
    do 5 iStepS.
    iFrame select (♢_)%I.
    iFrame select ($ _)%I.
    iExists l''.
    rewrite app_length /=.
    iSplitR. iPureIntro; lia.
    iFrame.
    rewrite insert_app_r_alt map_length /= // Nat.sub_diag.
    replace (length vs * 2 - length vs) with (1 + (length vs - 1)) by lia.
    replace (length vs * 2 - (length vs + 1)) with (length vs - 1) by lia.
    rewrite fmap_app -app_assoc /= left_id.
    iFrame.
Qed.

Definition vector_get : val :=
  λ: [["p", "i"]],
    let: "v" := "p".[0] in
    "v".["i"].

Lemma vector_get_spec `{!interpGS Σ} vs l cap i :
  i < length vs ->
  CODE (vector_get [[#l, ^i]])
  SOUV {[l]}
  PRE (Vector vs l cap)
  POST (fun r => ⌜r = (vs !!! i).1⌝ ∗ Vector vs l cap).
Proof.
  intros Hi.
  wps_call. iStepS.
  wps_bind. wps_load.
  unshelve wps_load. by rewrite app_length map_length; lia.
  iSplitR. iPureIntro.
  rewrite lookup_total_app_l //.
  now rewrite list_lookup_total_fmap //.
  now rewrite map_length.
  iExists _. iFrame.
  auto.
Qed.

(* When a goal is not convertible or equal to an Iris hypothesis
   ["H" : hyp], use [iExactEq ≡ "H"], which will replace your [goal]
   with [⌜goal ≡ hyp⌝] *)
Tactic Notation "iExactEq" "≡" constr(irisHyp) :=
  match goal with
  | |- environments.envs_entails ?Δ ?goal =>
    match Δ with
    | context[environments.Esnoc _ (INamed irisHyp) ?hyp] =>
      iAssert ⌜goal ≡ hyp⌝%I as %->; [ | iApply irisHyp ]
    end
  end.

(* Same with [=] instead of [≡] *)
Tactic Notation "iExactEq" "=" constr(irisHyp) :=
  match goal with
  | |- environments.envs_entails ?Δ ?goal =>
    match Δ with
    | context[environments.Esnoc _ (INamed irisHyp) ?hyp] =>
      iAssert ⌜goal = hyp⌝%I as %->; [ | iApply irisHyp ]
    end
  end.

(** Second spec for [vector_get] which provides a fraction of the
    stackable/mapsfrom assertions *)

Lemma vector_get_spec_borrow `{!interpGS Σ} vs l cap i :
  i < length vs ->
  CODE (vector_get [[#l, ^i]])
  SOUV {[l]}
  PRE (Vector vs l cap)
  POST (fun r =>
          let '(v, q) := vs !!! i in
          ⌜r = v⌝
        ∗ ∀ (q1 q2 : Qp),
          ⌜(q1 + q2 = q)%Qp⌝ →
          vStackable v q1
        ∗ v ↤?{q1} ∅
        ∗ Vector (<[i := (v, q2)]> vs) l cap
  ).
Proof.
  iIntros (Hi) "V".
  wps_apply vector_get_spec; auto.
  iDestruct select _ as "(-> & V)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & Hl & Sl' & Hl' & pl' & PS)".
  destruct (vs !!! i) as (v, q) eqn:Ei. iSplit; auto.
  iIntros (q1 q2 <-).

  iAssert (vStackable v q1 ∗ v ↤?{q1} ∅
   ∗ [∗ list] vq ∈ (<[i:=(v, q2)]> vs), let '(v, q) := vq in vStackable v q ∗ v ↤?{q} {[+ l' +]})%I
    with "[PS]" as "($ & $ & PS)".
  { iDestruct (big_sepL_insert_acc with "[$]") as "(PS & A)".
    apply list_lookup_lookup_total_lt; eauto.
    rewrite Ei. iDestruct "PS" as "((S1 & S2) & P)".
    iAssert (v ↤?{q1 + q2} (∅ ⊎ {[+ l' +]}))%I with "[P]" as "P".
    by rewrite left_id -Qp_to_Qz_plus_distr //.
    iDestruct (vmapsfrom_split with "P") as "(P1 & P2)".
    1,2 : by intros; edestruct Qp_not_zero; eauto.
    iFrame. iApply "A"; iFrame. }

  iExists _.
  rewrite insert_length.
  iFrame.
  iSplit; auto.
  iExactEq = "Hl'". iPureIntro. do 3 f_equal.
  apply list_eq; intros j.
  rewrite !list_lookup_fmap.
  destruct (decide (i = j)) as [<- | n].
  - rewrite !list_lookup_insert /= // list_lookup_lookup_total_lt /= // Ei //.
  - rewrite !list_lookup_insert_ne //.
Qed.

Definition vector_set : val :=
  λ: [["p", "i", "x"]],
    let: "v" := "p".[0] in
    "v".["i"] <- "x".

Lemma vector_set_spec `{!interpGS Σ} vs l cap i (x : val) (q : Qp) :
  i < length vs ->
  CODE (vector_set [[#l, ^i, x]])
  SOUV {[l]}
  PRE (vStackable x q
     ∗ x ↤?{q} ∅
     ∗ Vector vs l cap)
  POST (fun _ : () =>
       (let '(v,q) := vs !!! i in vStackable v q ∗ v ↤?{q} ∅ )
     ∗ Vector (<[i:=(x, q)]> vs) l cap).
Proof.
  intros Hi.
  iIntros "(Sx & ? & V)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & ? & ? & ? & ? & PS)".
  wps_nofree.
  wps_call.
  wps_bind. wps_load.
  unshelve (do 3 iStepS). by rewrite app_length map_length; lia.

  destruct (vs !!! i) as (v_, q_) eqn:Ei.

  iExists q, ∅. iFrame.
  iSplitR. iPureIntro; intro; apply Qp_not_zero.
  iIntros (_) "(? & Px & Pv)".

  iAssert (vStackable v_ q_ ∗ v_ ↤?{q_} {[+ l' +]} ∗
    [∗ list] vq ∈ (<[i:=(x, q)]> vs), let '(v,q) := vq in vStackable v q ∗ v ↤?{q} {[+ l' +]})%I
    with "[Px Sx PS]" as "(Sv_ & Pv_ & PS)".
  { iDestruct (big_sepL_insert_acc with "[$]") as "(PS & A)".
    apply list_lookup_lookup_total_lt; eauto.
    rewrite Ei. iDestruct "PS" as "($ & $)".
    rewrite left_id.
    iApply "A"; iFrame. }

  rewrite lookup_total_app_l /= // ?map_length //.
  rewrite list_lookup_total_fmap // Ei /=.
  iDestruct (vmapsfrom_join with "[$]") as "?".

  assert ({[+ l' +]} ⊎ {[-l'-]} ≡ (∅ : smultiset _)) as -> by smultiset_solver.
  rewrite right_id.
  iFrame.

  iExists l'. iFrame.
  rewrite insert_length insert_app_l /= ?map_length // list_fmap_insert.
  iFrame. auto.
Qed.

Definition vector_pop : val :=
  λ: [["p"]],
    let: "v" := "p".[0] in
    let: "cap" := "p".[1] in
    let: "size" := "p".[2] in
    let: "size" := "size" '- ^1 in
    let: "x" := "v".["size"] in
    "time_step" [[^1]];;
    "v".["size"] <- ();;
    "p".[2] <- "size";;
    let: "size_times_4" := "size" '* ^4 in
    let: "cap_small_enough" := "size_times_4" '- "cap" in
    (if: "cap_small_enough" then ()%V else
      let: "newcap" := if: "size" then "size" '* ^2 else (^1)%V in
      vector_resize [["p", "newcap"]]
    );;
    "x".

Lemma vector_pop_spec_no_resize `{!interpGS Σ} vs l cap (x : val) (q : Qp) time :
  cap < 4 * length vs ->
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (Vector (vs ++ [(x, q)]) l cap ∗ $ (S time))
  POST (fun r => ⌜r = x⌝
      ∗ vStackable x q
      ∗ x ↤?{q} ∅
      ∗ Vector vs l cap
      ∗ $ time).
Proof.
  iIntros (Hcap) "(V & T)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & ? & ? & ? & ? & PS)".
  wps_nofree.
  wps_call.
  wps_bind. wps_load.
  wps_bind. wps_load.
  wps_bind. wps_load.
  wps_bind. wps_val.
  wps_bind. wps_load.
  wps_bind. wps_apply time_step_spec.
  rewrite fmap_app -app_assoc list_lookup_total_middle ?app_length ?map_length /= //. 2:lia.
  rewrite !big_opL_snoc.
  iDestruct "PS" as "(PS & Sx & Px)".
  wps_bind. wps_store.
  wps_bind. wps_store.
  wps_bind. wps_val.
  wps_bind. wps_val.
  wps_bind. wps_if.
  destruct (decide _) as [i|i]; rewrite app_length /= in Hlen, i |- *. 2:lia.
  wps_val.
  rewrite list_lookup_total_middle ?app_length ?map_length /= //. 2:lia.
  iDestruct (vmapsfrom_join with "[$]") as "Px".
  assert ({[- l' -]} ⊎ {[+l'+]} ≡ (∅ : smultiset _)) as -> by smultiset_solver.
  rewrite left_id.
  wps_val. iSplitR; auto. iFrame "Sx Px".
  replace (length vs + 1 - 1) with (length vs) by lia.
  iFrame.
  iExists l'. iFrame.
  iStepS.
  set (b1 := BBlock _); set (b2 := BBlock _); assert (b1 = b2) as ->; auto. subst b1 b2; f_equal.
  rewrite insert_app_r_alt map_length // Nat.sub_diag /= -replicate_S. do 2 f_equal.
  lia.
Unshelve.
  rewrite !app_length map_length app_length /=. lia.
  rewrite !app_length map_length /=. lia.
Qed.

(** Transforms the goal [if C then wps X t1 Q else wps X t2 Q]
  into [Q (if C then v1 else v2)]
  if [t1] and [t2] can be proved to evaluate to [v1] and [v2] *)

Ltac wps_if_val v1 v2 :=
  match goal with
    |- environments.envs_entails ?E (if decide ?C then wps ?X ?t1 ?Q else wps ?X ?t2 ?Q) =>
      cut (environments.envs_entails E (Q (if decide C then v1 else v2)));
      [ destruct (decide C); intro; wps_val; assumption | ]
  end.

(** Transforms [if C then (f A) else (f B)] into [f (if C then A else B)] *)

Ltac fold_if :=
  match goal with
    |- context[if ?C then (?f ?A) else (?f ?B)] =>
      replace (if C then (f A) else (f B))
      with (f (if C then A else B))
      by now destruct C
  end.

Lemma vector_pop_spec_resize `{!interpGS Σ} vs l cap (x : val) (q : Qp) time :
  cap >= 4 * length vs ->
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (Vector (vs ++ [(x, q)]) l cap
      ∗ ♢(1 `max` (length vs * 2))%nat
      ∗ $ (S (1 `max` (length vs * 2)) + (length vs + time)))
  POST (fun r => ⌜r = x⌝
      ∗ vStackable x q
      ∗ x ↤?{q} ∅
      ∗ Vector vs l (1 `max` (length vs * 2))
      ∗ ♢cap
      ∗ $ time).
Proof.
  iIntros (Hcap) "(V & dia & T)".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & ? & ? & ? & ? & PS)".
  wps_call.
  wps_bind. wps_load.
  wps_bind. wps_load. iIntros "?".
  wps_bind. wps_load. iIntros "?".
  wps_bind. wps_val. iIntros "?".
  wps_bind. wps_load. iIntros "?".
  rewrite fmap_app -app_assoc list_lookup_total_middle ?app_length ?map_length /= //. 2:lia.
  rewrite !big_opL_snoc.
  iDestruct "PS" as "(PS & Sx & Px)".
  replace (length vs + 1 - 1) with (length vs) by lia.
  wps_bind. wps_apply time_step_spec. iIntros.
  wps_bind. Fail wps_store. do 7 iStepS.
  wps_bind. Fail wps_store. do 7 iStepS.
  wps_bind. wps_val. iIntros "?".
  wps_bind. wps_val. iIntros "?".
  wps_bind. wps_if.
  destruct (decide _) as [i|i]; rewrite app_length /= in Hlen, i |- *. lia.
  wps_bind. wps_if.

  wps_if_val (length vs * 2)%V 1%V.
  rewrite insert_app_r_alt; rewrite map_length//.
  rewrite Nat.sub_diag /= -replicate_S.
  replace (S (cap - (length vs + 1))) with (cap - length vs) by lia.
  fold_if.

  wps_apply (vector_resize_spec vs). 1,2: destruct vs; simpl; lia.
  rewrite list_lookup_total_middle ?app_length ?map_length /= //.
  iDestruct (vmapsfrom_join with "[$]") as "Px".
  assert ({[- l' -]} ⊎ {[+l'+]} ≡ (∅ : smultiset _)) as -> by smultiset_solver.
  rewrite left_id.
  rew_qz.
  assert (1 `max` (length vs * 2) = if decide (length vs ≠ 0) then (length vs * 2) else 1)%nat
     as E by (destruct (decide _) as [h|h]; lia).
  rewrite -E.
  iFrame.
  iSplitR "Px".
  { iFrame. iExists l'. iFrame. iPureIntro; lia. }
  iIntros (_) "(V&?) Sx".
  iDestruct "V" as (l'') "((%Hlen' & %Pcap') & Hl & Sl' & Hl' & pl' & PS)".
  wps_val. iSplitR; auto. iFrame.
  iExists l''. iFrame. auto.
Unshelve.
  rewrite !app_length map_length app_length /=. lia.
  rewrite !app_length map_length /=. lia.
Qed.

Lemma vector_pop_joined_specs `{!interpGS Σ} vs l cap (x : val) (q : Qp) time :
  let cond := decide (4 * length vs <= cap) in
  let newcap := 1 `max` (length vs * 2) in
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (Vector (vs ++ [(x, q)]) l cap
      ∗ (if cond then ♢newcap else True)
      ∗ $ (if cond then S (1 `max` (length vs * 2)) + (length vs + time) else S time)%nat)
  POST (fun r => ⌜r = x⌝
      ∗ vStackable x q
      ∗ x ↤?{q} ∅
      ∗ Vector vs l (if cond then newcap else cap)
      ∗ (if cond then ♢cap else True)
      ∗ $ time).
Proof.
  destruct (decide _).
  - apply vector_pop_spec_resize; auto.
  - iIntros "(V & ? & ?)". wps_apply vector_pop_spec_no_resize. lia. iFrame.
Qed.

Lemma vector_pop_joined_specs_lookup `{!interpGS Σ} vs l cap time :
  vs ≠ [] ->
  let cond := decide (4 * (length vs - 1) <= cap) in
  let newcap := 1 `max` ((length vs - 1) * 2) in
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (Vector vs l cap
      ∗ (if cond then ♢newcap else True)
      ∗ $ (if cond then S newcap + (length vs - 1 + time) else S time)%nat)
  POST (fun r =>
        let '(x, q) := vs !!! (length vs - 1) in
        ⌜r = x⌝
      ∗ vStackable x q
      ∗ x ↤?{q} ∅
      ∗ Vector (rev (tail (rev vs))) l (if cond then newcap else cap)
      ∗ (if cond then ♢cap else True)
      ∗ $ time).
Proof.
  intros Hvs.
  rewrite -(rev_involutive vs) in Hvs |- *.
  destruct (rev vs) as [ | (x, q) ? ]. tauto.
  iIntros "(V & d & T)".
  simpl rev.
  rewrite list_lookup_total_middle ?app_length ?Nat.add_sub //.
  wps_apply (vector_pop_joined_specs (rev l0) l cap x q).
  rewrite rev_app_distr /= rev_involutive //.
Qed.

(** note: here, but already in the pop/push specifications with resize, time for
    freeing and garbage collection was not accounted for. *)

Lemma vector_free `{!interpGS Σ} vs l cap :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ Vector vs l cap =#=∗
  ♢(cap + 3) ∗ †l
  ∗ ([∗ list] vq ∈ vs, let '(v,q) := vq in vStackable v q ∗ v ↤?{q} ∅).
Proof.
  iIntros "(Sl & Pl & V)".
  iIntros (? ? ?) "I".
  iDestruct "V" as (l') "((%Hlen & %Pcap) & Hl & Sl' & Hl' & pl' & PS)".
  iMod (@interp_free _ _ _ k σ _ ∅ l with "[$]") as "(Hi & ? & #dl)".
  { set_solver. }
  { set_solver. }
  iMod (mapsfrom_cleanup with "[$] [$]") as "(? & ?)".
  rewrite -opposite_singleton opposite_cancel.
  iMod (@interp_free _ _ _ k σ _ ∅ l' with "[$]") as "(Hi & ? & #dl')".
  { set_solver. }
  { set_solver. }
  iDestruct (diamonds_join with "[$]") as "dia".
  rewrite /size_block app_length replicate_length map_length. simpl length. rew_qz.
  replace (length vs + (cap - length vs) + 3) with (cap + 3) by lia.
  iFrame "dia dl".
  clear Hlen.

  iPoseProof (vmapsfroms_val_Qp_cleanup_supd true _ l' _ {[+ l' +]} with "[$] Hi")
    as ">($ & Pvs)".
  rewrite big_sepL_proper. auto.
  intros ? (?, ?) ?. rewrite -opposite_singleton opposite_cancel //.
Qed.


(** Amortized specifications *)

Parameter time_credit_join : forall `{!interpGS Σ} (n m : nat),
  ($ n ∗ $ m -∗ $ (n + m)).

Parameter time_credit_split : forall `{!interpGS Σ} (n m : nat),
  ($ (n + m) -∗ $ n ∗ $ m).

Lemma time_credit_split_alt `{!interpGS Σ} (n m : nat) :
  n <= m -> ($ m -∗ ($ n ∗ $ (m - n))).
Proof.
  iIntros (L) "T".
  replace m with (n + (m - n)) at 1 by lia.
  iDestruct (time_credit_split with "T") as "($ & $)".
Qed.

Lemma time_credit_split_3 `{!interpGS Σ} (n m l: nat) :
  ($ (n + m + l) -∗ $ n ∗ $ m ∗ $ l).
Proof.
  iIntros "d".
  iDestruct (time_credit_split with "[$]") as "(? & $)".
  iDestruct (time_credit_split with "[$]") as "($ & $)".
Qed.

Lemma time_credit_weak `{!interpGS Σ} (n m : nat) :
  n <= m -> ($ m -∗ $ n).
Proof.
  iIntros (L) "T". replace m with (n + (m - n)) by lia.
  iDestruct (time_credit_split with "T") as "($ & _)".
Qed.

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
