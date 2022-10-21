From stdpp Require Import decidable binders gmultiset.
From iris.proofmode Require Import proofmode.

From iris.algebra Require Import gmap.

From spacelambda.language Require Import notation.

From spacelambda Require Import more_space_lang wp_all triple.

From spacelambda.examples Require Export tactics utils diaframe.

Definition Vector `{!interpGS Σ} (qz : Qz) (qp : Qp) (vs : list val) (l : loc) (capacity : nat) : iProp Σ :=
  ∃ (l' : loc),
    ⌜ length vs <= capacity ⌝
    ∗ ⌜ 0 < capacity ⌝ (* easier than doing "max 1 n" *)
    ∗ l ↦ BBlock [ ^capacity; ^(length vs); #l' ]
    ∗ Stackable l' 1%Qp
    ∗ l' ↦ BBlock (vs ++ replicate (capacity - length vs) ())
    ∗ l' ↤ {[+ l +]}
    ∗ ([∗ list] v ∈ vs, v ↤?{qz} {[+ l' +]})
    ∗ ([∗ list] v ∈ vs, vStackable v qp).

Definition vector_create : val :=
  λ: [["n"]],
    let: "c" := alloc 3 in
    "c".[0] <- "n" ;;
    "c".[1] <- ^0 ;;
    let: "v" := alloc "n" in
    "c".[2] <- "v" ;;
    "c".

Lemma vector_create_spec `{!interpGS Σ} (n : nat) qz qp :
  0 < n ->
  CODE (vector_create [[^n]])
  PRE (♢ (3 + n))
  POST (fun (l:loc) => Vector qz qp [] l n ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  iIntros (?) "?".
  wps_call.
  wps_bind. wps_alloc l as "(? & ? & ? & ?)".
  wps_bind. (* Fail wps_store. *) do 7 iStepS.
  wps_bind. (* Fail wps_store. *) do 7 iStepS.
  wps_bind. wps_alloc l'. do 1 iStepS.
  wps_bind. wps_store. do 3 iStepS.
  iFrame.

  rew_qz. replace (3 + n - 3 - n)%nat with 0 by lia.
  iExists l'. rewrite Nat.sub_0_r /= left_id. iFrame.
  iPureIntro; lia.
Qed.

Definition array_copy : val :=
  μ: "self", [["dst", "src", "i", "n"]],
    let: "eq" := "n" '== "i" in
    if: "eq" then ()%V
    else
      let: "x" := "src".["i"] in
      "dst".["i"] <- "x";;
      let: "i" := "i" '+ 1 in
      "self" [["dst", "src", "i", "n"]].

Lemma array_copy_spec `{!interpGS Σ} dst src qz src1 src2 src3 dst1 dst3 :
  qz ≠ 0%Qz ->
  length src1 = length dst1 ->
  CODE (array_copy [[#dst, #src, ^(length src1), ^(length src1 + length src2)]])
  SOUV {[dst; src]}
  PRE (src ↦ BBlock (src1 ++ src2 ++ src3)
     ∗ dst ↦ BBlock (dst1 ++ replicate (length src2) () ++ dst3)
     ∗ [∗ list] v ∈ src2, v ↤?{qz} {[+ src +]})
  POST (fun _ =>
       src ↦ BBlock (src1 ++ src2 ++ src3)
     ∗ dst ↦ BBlock (dst1 ++ src2 ++ dst3)
     ∗ [∗ list] v ∈ src2, v ↤?{qz} {[+ src; dst +]}).
Proof.
  iIntros (Hqz E1).
  iInduction (src2) as [ | v src2 ] "IH" forall (src1 src3 dst1 dst3 Hqz E1);
    iIntros "(? & ? & ?)".
  - wps_call.
    (* we establish that the condition is false *)
    wps_bind. wps_call.
    rewrite Nat.add_0_r.
    wps_if. rewrite bool_decide_eq_true_2 //.
    wps_val.
    iFrame.

  - wps_call.
    iDestruct select (_ ∗ _)%I  as "(? & ?)".
    (* we establish that the condition is true *)
    wps_bind. wps_call.
    wps_if.
    rewrite bool_decide_eq_false_2; last lia.

    (* loads v *)
    wps_bind.
    unshelve wps_load.
    { rewrite app_length /=; lia. }
    rewrite list_lookup_total_middle //.
    (* stores v then unit *)
    wps_bind. unshelve wps_store. by rewrite app_length /=; lia.

    (* the store introduced some extra vmapsfroms, one of them being for unit *)
    rewrite !list_lookup_total_middle /= //. iClear select True%I.

    (* i+1 *)
    wps_bind. wps_call.

    (* massaging to match the I.H. *)
    replace (length src1 + 1) with (length (src1 ++ [v])) by now rewrite app_length /=; lia.
    replace (length src1 + _) with (length (src1 ++ [v]) + length src2) by now rewrite app_length /=; lia.
    rewrite insert_app_r_alt /=. 2:lia. replace (_ - _) with O by lia. simpl.
    rewrite (cons_middle _ dst1) (app_assoc dst1).
    rewrite (cons_middle _ src1) (app_assoc src1).
    assert (length (src1 ++ [v]) = length (dst1 ++ [v])) by now rewrite !app_length /=; lia.

    (* we can finally apply the induction hypothesis -- only thing to be framed is v's mapsfrom *)
    wps_apply "IH"; auto.
    rewrite -!app_assoc.
    iFrame.
Qed.


Definition vector_resize : val :=
  λ: [["p", "newcap"]],
    let: "size" := "p".[1] in
    let: "oldv" := "p".[2] in
    let: "newv" := alloc "newcap" in
    array_copy [["newv", "oldv", ^0, "size"]];;
    "p".[2] <- "newv";;
    "p".[0] <- "newcap".

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

Lemma vector_resize_spec `{!interpGS Σ} qz qp vs (oldcap newcap : nat) l :
  qz ≠ 0%Qz ->
  oldcap <= newcap ->
  CODE (vector_resize [[#l, ^newcap]])
  SOUV {[l]}
  PRE (Vector qz qp vs l oldcap ∗ ♢newcap)
  POST (fun _ => Vector qz qp vs l newcap ∗ ♢oldcap).
Proof.
  iIntros (Hqz L) "(V & ?)".
  iDestruct "V" as (l') "(% & % & Hl & Sl' & Hl' & pl' & MP & S)".
  wps_call.
  wps_bind. wps_load. iIntros.
  wps_bind. wps_load. iIntros.
  wps_bind. wps_alloc l'' as  "(dia & Hl'' & pl'' & Sl'')".
  iIntros "Sl'".
  iPoseProof
    (array_copy_spec l'' l' qz nil vs
       (replicate (oldcap - length vs) ()%V) nil
       (replicate (newcap - length vs) ()%V)
      with "[Hl' MP Hl'']") as "A"; auto;
  [ rewrite -replicate_plus;
    replace (length vs + (newcap - length vs)) with newcap by lia;
    iFrame; auto | ].

  wps_bind.
  iApply (wps_context_singleton l'). iFrame.
  iApply (@wps_weak _ _ _ _  {[l''; l']}). now multiset_solver.
  iApply (wps_mono with "A").
  iIntros (_) "(?&?&Pvs) ?".
  iIntros "?".
  wps_bind. wps_store.
  assert ({[-l-]} ⊎ {[+l+]} ≡ ∅) as -> by smultiset_solver.
  rew_qz. simpl plus.
  iApply (wps_confront_Stackable l' with "[$]"). iIntros "% ?".
  wps_free l' as "(? & #dl')".

  iApply (wps_esupd _ _ _ _ (vmapsfroms_cleanup_supd true _ l' _ _ _)).
  iSplitL "Pvs". by iFrame. iIntros "Pvs".
  do 6 iStepS.
  rewrite left_id.
  rewrite /= app_length replicate_length.
  replace (length vs + (oldcap - length vs)) with oldcap by lia.
  iFrame.
  iExists _; iFrame.
  iSplitR. iPureIntro; lia.
  iSplitR. iPureIntro; lia.
  rewrite big_sepL_proper. iFrame.
  intros ? ? ?.
  assert (({[+ l'; l'' +]} ⊎ {[-l'-]} : smultiset _)
            ≡ {[+ l'' +]}) as -> by smultiset_solver.
  auto.
  Unshelve.
  set_solver.
Qed.

Definition vector_push : val :=
  λ: [["p", "x"]],
    let: "cap" := "p".[0] in
    let: "size" := "p".[1] in
    let: "eq" := "cap" '== "size" in
    (if: "eq" then
       let: "newcap" := "cap" '* 2 in
       vector_resize [["p", "newcap"]]
     else ()%V );;
    let: "v" := "p".[2] in
    "v".["size"] <- "x";;
    let: "size" := "size" '+ 1 in
    "p".[1] <- "size".

Lemma vector_push_spec_no_resize `{!interpGS Σ} qz qp vs l v cap :
  qz ≠ 0%Qz ->
  length vs < cap ->
  CODE (vector_push [[#l, v]])
  SOUV {[l]}
  PRE (vStackable v qp ∗ v ↤?{qz} ∅ ∗ Vector qz qp vs l cap)
  POST (fun _ => Vector qz qp (vs ++ [v]) l cap).
Proof.
  iIntros (Hqz Hvs) "(Sv & pv & V)".
  iDestruct "V" as (l') "(%len & % & Hl & Sl' & Hl' & pl' & pvs & Svs)".
  wps_call.
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. wps_call; [ .. | iIntros "Sv"].
  wps_bind. wps_if. rewrite bool_decide_eq_false_2; last lia.
  wps_val. iIntros "Sv".
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. unshelve wps_store; [ .. | ].
  now rewrite app_length replicate_length; lia.
  wps_bind. wps_call; [ .. | ].
  do 6 iStepS.
  iExists l'.
  rewrite app_length /=.
  iSplitR. now iPureIntro; lia.
  iSplitR. easy.
  iFrame.
  rewrite insert_app_r_alt /= // Nat.sub_diag.
  replace (cap - length vs) with (1 + (cap - (length vs + 1))) by lia.
  rewrite -app_assoc /= left_id.
  iFrame.
Qed.

Lemma vector_push_spec_resize `{!interpGS Σ} qz qp vs l v cap :
  qz ≠ 0%Qz ->
  length vs = cap ->
  CODE (vector_push [[#l, v]])
  SOUV {[l]}
  PRE (vStackable v qp ∗ v ↤?{qz} ∅ ∗ Vector qz qp vs l cap ∗ ♢(length vs * 2))
  POST (fun _ => Vector qz qp (vs ++ [v]) l (cap * 2) ∗ ♢(length vs)).
Proof.
  iIntros (Hqz Hvs) "(Sv & pv & V & dia)".
  iDestruct "V" as (l') "(%len & % & Hl & Sl' & Hl' & pl' & pvs & Svs)".
  wps_call.
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. wps_load; [ .. | iIntros "Sv"].
  wps_bind. wps_call; [ .. | iIntros "Sv"].
  wps_bind. wps_if. rewrite bool_decide_eq_true_2 //.
  wps_bind. wps_call.
  assert (length vs <= length vs * 2) as A by lia.
  wps_apply vector_resize_spec. eassumption. eassumption.
  rew_qz. iFrame.
  iSplitR "pv".
  + iExists l'. iFrame.
    iSplitR; auto.
  + iIntros (_) "(V&?) ?".
    iDestruct "V" as (l'') "(% & % & Hl & Sl' & Hl' & pl' & pvs & Svs)".
    wps_bind. wps_load. iIntros "?".
    wps_bind. unshelve wps_store.
    { rewrite app_length replicate_length. lia. }
    wps_bind. wps_call.
    do 6 iStepS.
    iFrame select (♢_)%I.
    iExists l''.
    rewrite app_length /=.
    iSplitR. now iPureIntro; lia.
    iSplitR. easy.
    iFrame.
    rewrite insert_app_r_alt /= // Nat.sub_diag.
    replace (length vs * 2 - length vs) with (1 + (length vs - 1))%nat by lia.
    replace (length vs * 2 - (length vs + 1)) with (length vs - 1)%nat by lia.
    rewrite -app_assoc /= left_id.
    iFrame.
Qed.

Definition vector_get : val :=
  λ: [["p", "i"]],
    let: "v" := "p".[2] in
    "v".["i"].

Lemma vector_get_spec `{!interpGS Σ} qz qp vs l cap i :
  i < length vs ->
  CODE (vector_get [[#l, ^i]])
  SOUV {[l]}
  PRE (Vector qz qp vs l cap)
  POST (fun r => ⌜r = vs !!! i⌝ ∗ Vector qz qp vs l cap).
Proof.
  intros Hi.
  wps_call. iStepS.
  wps_bind. wps_load.
  unshelve wps_load. by rewrite app_length; lia.
  iSplitR. iPureIntro. by rewrite lookup_total_app_l //.
  iExists _. iFrame.
  auto.
Qed.

Definition vector_set : val :=
  λ: [["p", "i", "x"]],
    let: "v" := "p".[2] in
    "v".["i"] <- "x".

Lemma vector_set_spec `{!interpGS Σ} qz qp vs l cap i (x : val) :
  qz ≠ 0%Qz ->
  i < length vs ->
  CODE (vector_set [[#l, ^i, x]])
  SOUV {[l]}
  PRE (vStackable x qp
     ∗ x ↤?{qz} ∅
     ∗ Vector qz qp vs l cap)
  POST (fun r =>
       vStackable (vs !!! i) qp
     ∗ (vs !!! i) ↤?{qz} ∅
     ∗ Vector qz qp (<[i:=x]> vs) l cap).
Proof.
  intros Hqz Hi.
  iIntros "(? & ? & V)".
  iDestruct "V" as (l') "(% & % & ? & ? & ? & ? & Pvs & Svs)".
  wps_call.
  wps_bind. wps_load. iIntros "Sx".
  unshelve (do 4 iStepS). by rewrite app_length; lia.

  iAssert (vStackable (vs !!! i) qp ∗
    [∗ list] v ∈ (<[i:=x]> vs), vStackable v qp)%I
    with "[Sx Svs]" as "(Sv & Svs)".
  { iDestruct (big_sepL_insert_acc with "[$]") as "($ & A)".
    apply list_lookup_lookup_total_lt; auto.
    iApply "A"; auto. }

  iExists qz, ∅. iFrame.
  iSplitR. iPureIntro; auto.
  iIntros (_) "(? & Px & Pv)".

  iAssert ((vs !!! i) ↤?{qz} {[+ l' +]}∗
    [∗ list] v ∈ <[i:=x]> vs, v ↤?{qz} {[+ l' +]})%I
    with "[Px Pvs]" as "(Pv2 & Pvs)".
  { rewrite left_id.
    iDestruct (big_sepL_insert_acc with "[$]") as "($ & A)".
    apply list_lookup_lookup_total_lt; eauto.
    iApply "A"; auto. }

  rewrite lookup_total_app_l /= //.
  iDestruct (vmapsfrom_join with "[$]") as "?".

  assert ({[+ l' +]} ⊎ {[-l'-]} ≡ (∅ : smultiset _)) as -> by smultiset_solver.
  rewrite right_id.
  iFrame.

  iExists l'. iFrame.
  rewrite insert_length insert_app_l /= //.
  iFrame. auto.
Qed.

Definition vector_pop : val :=
  λ: [["p"]],
    let: "v" := "p".[2] in
    let: "size" := "p".[1] in
    let: "size" := "size" '- 1 in
    let: "x" := "v".["size"] in
    "p".[1] <- "size";;
    "v".["size"] <- ();;
    "x".

Lemma diamonds_le `{!interpGS Σ} n m : n <= m -> ♢ m -∗ ♢ n.
Proof.
  intros.
  replace m with (n + (m - n)) by lia.
  rewrite nat_to_Qz_add diamond_split_iff.
  iIntros "($ & ?)".
Qed.

Lemma vector_pop_spec `{!interpGS Σ} qz qp vs l cap (x : val) :
  qz ≠ 0%Qz ->
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (Vector qz qp (vs ++ [x]) l cap)
  POST (fun r => ⌜r = x⌝
      ∗ vStackable x qp
      ∗ x ↤?{qz} ∅
      ∗ Vector qz qp vs l cap).
Proof.
  intros Hqz.
  iIntros "V".
  iDestruct "V" as (l') "(% & % & ? & ? & ? & ? & Pvs & Svs)".
  wps_call.
  wps_bind. wps_load.
  wps_bind. wps_load. iIntros "?".
  wps_bind. wps_call. iIntros "?".
  wps_bind. wps_store.
  rewrite !big_opL_snoc app_length /= Nat.add_sub.
  rewrite -app_assoc list_lookup_total_middle //.
  iDestruct "Pvs" as "(Pvs & Px)".
  iDestruct "Svs" as "(Svs & Sx)".

  wps_bind. wps_store.
  wps_bind. wps_store.
  rewrite list_lookup_total_middle //.
  iDestruct (vmapsfrom_join with "[$]") as "?".
  assert ({[- l' -]} ⊎ {[+l'+]} ≡ (∅ : smultiset _)) as -> by smultiset_solver.
  rewrite left_id.
  iStepS.
  iStepS.
  iStepS.
  iStepS.

  iExists l'. iFrame.
  iStepS.
  iStepS.
  set (b1 := BBlock _); set (b2 := BBlock _); assert (b1 = b2) as ->; auto. subst b1 b2; f_equal.
  rewrite insert_app_r_alt // Nat.sub_diag /= -replicate_S. do 2 f_equal.
  rewrite ->app_length in *. simpl in *. lia.
Unshelve.
  rewrite !app_length /=. lia.
  rewrite !app_length /=. lia.
  rewrite ->app_length in *. simpl in *. lia.
Qed.

Lemma vector_free `{!interpGS Σ} qz qp vs l cap :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ Vector qz qp vs l cap =#=∗
  ♢(cap + 3) ∗ †l
    ∗ ([∗ list] v ∈ vs, v ↤?{qz} ∅)
    ∗ ([∗ list] v ∈ vs, vStackable v qp).
Proof.
  iIntros "(Sl & Pl & V)".
  iIntros (? ? ?) "I".
  iDestruct "V" as (l') "(%len & % & Hl & Sl' & Hl' & pl' & pvs & Svs)".
  iMod (@interp_free _ _ _ k σ _ ∅ l with "[$]") as "(Hi & ? & #dl)".
  { set_solver. }
  { set_solver. }
  iMod (mapsfrom_cleanup with "[$] [$]") as "(? & ?)".
  rewrite -opposite_singleton opposite_cancel.
  iMod (@interp_free _ _ _ k σ _ ∅ l' with "[$]") as "(Hi & ? & #dl')".
  { set_solver. }
  { set_solver. }
  iDestruct (diamonds_join with "[$]") as "dia".
  rewrite /size_block app_length replicate_length. simpl length. rew_qz.
  replace (length vs + (cap - length vs) + 3) with (cap + 3) by lia.
  iFrame "Svs dia dl".
  clear len.

  iPoseProof (vmapsfroms_cleanup_supd true _ l' _ {[+ l' +]} _ with "[$] Hi")
    as ">($ & Pvs)".
  rewrite big_sepL_proper. auto.
  intros ? ? ?. rewrite -opposite_singleton opposite_cancel //.
Qed.

Ltac gather_diamonds := repeat (iDestruct (diamonds_join with "[$]") as "?"; rew_qz; simpl Nat.add).

Example example `{!interpGS Σ} :
  CODE (
      let: "v" := vector_create [[^1]] in
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
      let: "x" := vector_pop [["v"]] in
      "x"
    )
  PRE (♢19)
  POST (fun res : val => ⌜res = 4⌝ ∗ ♢19).
Proof.
  iIntros "?".
  mine 4. wps_bind. wps_apply (vector_create_spec 1 1 1). auto. rew_qz. iStepS. iIntros (l) "(V & S & Pl)".
  wps_bind. wps_apply vector_push_spec_no_resize; auto. iIntros "?".
  mine 2.
  wps_bind. wps_apply vector_push_spec_resize; auto. rew_qz. simpl. iFrame. iIntros (_) "(? & ?) ?".
  gather_diamonds. mine 4.
  wps_bind. wps_apply vector_push_spec_resize; auto. rew_qz. simpl. iFrame. iIntros (_) "(? & ?) ?".
  wps_bind. wps_apply vector_push_spec_no_resize; auto. iIntros "?".
  gather_diamonds. mine 8.
  wps_bind. wps_apply vector_push_spec_resize; auto. rew_qz. simpl. iFrame. iIntros (_) "(? & ?) ?".
  wps_bind. wps_apply vector_push_spec_no_resize. auto. auto. iIntros "?".
  wps_bind. wps_apply vector_push_spec_no_resize. auto. auto. iIntros "?".
  wps_bind. wps_apply vector_set_spec. auto. simpl; lia. iIntros "?".
  wps_bind. wps_apply vector_set_spec. auto. simpl; lia. iIntros "?".
  wps_bind. wps_apply vector_set_spec. auto. simpl; lia. iIntros "?".
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  wps_bind. wps_apply (vector_pop_spec 1 1 [(^11)%V; (^22)%V; (^3)%V; (^4)%V; (^5)%V; (^6)%V] l). auto. iIntros "?".
  iDestruct select (_ ∗ _)%I as "(-> & % & % & ?)".
  wps_bind. wps_apply (vector_pop_spec 1 1 [(^11)%V; (^22)%V; (^3)%V; (^4)%V; (^5)%V] l). auto. iIntros "?".
  iDestruct select (_ ∗ _)%I as "(-> & % & % & ?)".
  wps_bind. wps_apply (vector_pop_spec 1 1 [(^11)%V; (^22)%V; (^3)%V; (^4)%V] l). auto. iIntros "?".
  iDestruct select (_ ∗ _)%I as "(-> & % & % & ?)".
  wps_bind.
  iApply (wps_context_singleton l). iFrame.
  wps_apply (vector_pop_spec 1 1 [(^11)%V; (^22)%V; (^3)%V] l). auto. iIntros "?".
  iDestruct select (_ ∗ _)%I as "(-> & % & % & ?)".
  iApply (wps_esupd _ _ _ _ (vector_free 1 1 [(^11)%V; (^22)%V; (^3)%V] l 8) with "[-]").
  iFrame. iIntros "(? & ? & ? & ? & ?)".
  gather_diamonds.
  subst. wps_val. auto.
  Unshelve.
  set_solver.
Qed.

(** Amortized *)

Definition VectorAm `{!interpGS Σ} (qz : Qz) (qp : Qp) (vs : list val) (l : loc) : iProp Σ :=
  ∃ (capacity : nat),
    ♢ (length vs * 3 - capacity)%nat
    ∗ Vector qz qp vs l capacity.

Lemma vector_create_amortized_spec `{!interpGS Σ} (n : nat) qz qp :
  0 < n ->
  CODE (vector_create [[^n]])
  PRE (♢ (3 + n))
  POST (fun (l:loc) => VectorAm qz qp [] l ∗ Stackable l 1%Qp ∗ l ↤ ∅).
Proof.
  iIntros (?) "dia".
  iApply wps_bupd. iMod diamonds_zero. iModIntro.
  iPoseProof (vector_create_spec n qz qp with "dia") as "A"; auto.
  iApply (wps_mono with "A").
  iIntros (l) "(V & $ & $)".
  iExists n; auto.
Qed.

Lemma vector_push_amortized_spec `{!interpGS Σ} qz qp vs l v :
  qz ≠ 0%Qz ->
  CODE (vector_push [[#l, v]])
  SOUV {[l]}
  PRE (vStackable v qp ∗ v ↤?{qz} ∅ ∗ VectorAm qz qp vs l ∗ ♢3)
  POST (fun _ => VectorAm qz qp (vs ++ [v]) l).
Proof.
  iIntros (Hqz) "(Sv & pv & V & dia)".
  iDestruct "V" as (cap) "(dn & V)".
  destruct (decide (length vs < cap)).
  - iPoseProof (vector_push_spec_no_resize qz with "[$]") as "A"; auto.
    iApply (wps_mono with "A"). iIntros (_) "V".
    iExists cap. iFrame. gather_diamonds. iApply (diamonds_le with "[$]").
    rewrite app_length /= //. lia.
  - iAssert ⌜length vs ≤ cap⌝%I as "%". by iDestruct "V" as (?) "($ & ?)".
    assert (cap = length vs) as -> by lia.
    replace (length vs * 3 - length vs) with (length vs * 2) by lia.
    iPoseProof (vector_push_spec_resize qz with "[$Sv $pv $V dn]") as "A"; auto. by rew_qz.
    iApply (wps_mono with "A"). iIntros (_) "(V & d)".
    iExists (length vs * 2). iFrame. gather_diamonds. iApply (diamonds_le with "[$]").
    rewrite app_length /= //. lia.
Qed.

Lemma vector_set_amortized_spec `{!interpGS Σ} qz qp vs l i (x : val) :
  qz ≠ 0%Qz ->
  i < length vs ->
  CODE (vector_set [[#l, ^i, x]])
  SOUV {[l]}
  PRE (vStackable x qp
     ∗ x ↤?{qz} ∅
     ∗ VectorAm qz qp vs l)
  POST (fun r =>
       vStackable (vs !!! i) qp
     ∗ (vs !!! i) ↤?{qz} ∅
     ∗ VectorAm qz qp (<[i:=x]> vs) l).
Proof.
  iIntros (Hqz Hi) "(? & ? & V)".
  iDestruct "V" as (cap) "(? & V)".
  iPoseProof (vector_set_spec qz qp vs l cap i x with "[$]") as "A"; auto.
  iApply (wps_mono with "A").
  iIntros (?) "($ & $ & V)".
  iExists cap; iFrame.
  rewrite insert_length //.
Qed.

Lemma vector_get_amortized_spec `{!interpGS Σ} qz qp vs l i :
  i < length vs ->
  CODE (vector_get [[#l, ^i]])
  SOUV {[l]}
  PRE (VectorAm qz qp vs l)
  POST (fun r => ⌜r = vs !!! i⌝ ∗ VectorAm qz qp vs l).
Proof.
  iIntros (Hi) "V".
  iDestruct "V" as (cap) "(? & V)".
  iPoseProof (vector_get_spec qz qp vs l cap i with "[$]") as "A"; auto.
  iApply (wps_mono with "A").
  iIntros (?) "($ & V)".
  iExists cap; iFrame.
Qed.

Lemma vector_pop_amortized_spec `{!interpGS Σ} qz qp vs l (x : val) :
  qz ≠ 0%Qz ->
  CODE (vector_pop [[#l]])
  SOUV {[l]}
  PRE (VectorAm qz qp (vs ++ [x]) l)
  POST (fun r => ⌜r = x⌝
      ∗ vStackable x qp
      ∗ x ↤?{qz} ∅
      ∗ VectorAm qz qp vs l).
Proof.
  iIntros (Hqz) "V".
  iDestruct "V" as (cap) "(? & V)".
  iPoseProof (vector_pop_spec qz qp vs l cap with "[$]") as "A"; auto.
  iApply (wps_mono with "A").
  iIntros (?) "($ & $ & $ & V)".
  iExists cap; iFrame.
  iApply (diamonds_le with "[$]"). rewrite app_length. lia.
Qed.

Lemma vector_free_amortized  `{!interpGS Σ} qz qp vs l :
  Stackable l 1%Qp ∗ l ↤ ∅ ∗ VectorAm qz qp vs l =#=∗
  ♢(3 + length vs) ∗ †l
    ∗ ([∗ list] v ∈ vs, v ↤?{qz} ∅)
    ∗ ([∗ list] v ∈ vs, vStackable v qp).
Proof.
  iIntros "(Sl & Pl & V)".
  iIntros (? ? σ) "Hi".
  iDestruct "V" as (cap) "(? & V)".
  iPoseProof (vector_free  qz qp vs l cap
               with "[$Sl $Pl $V] Hi")
    as ">(Hi & Sk & ? & ? & ?)".
  iFrame.
  gather_diamonds. iModIntro.
  iApply (diamonds_le with "[$]").
  lia.
Qed.
