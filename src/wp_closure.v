From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap binders gmultiset stringmap.

From spacelambda.fracz Require Import qz.
From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language closure.

From spacelambda Require Import more_maps_and_sets more_space_lang.
From spacelambda Require Import utils interp wp_alloc wp_store wp_load wp_call.

From diaframe Require Import proofmode_base.

Section Closure.
Context `{interpGS Σ}.

Definition IsClosureAux (env:list val) (lq:list Qz) (self:string) (args:list binder) (code:tm) (l:loc) : iProp Σ :=
  let fv := fv_clo self args code in
  l ↦ BBlock ((code_clo self args code fv)::env) ∗
    ⌜self ∉ set_of_args args⌝ ∗ ⌜length env = length fv⌝ ∗
    ⌜locs code = ∅⌝ ∗
    group_pointedbys {[+l+]} env lq.

Lemma subst_blk_clo_init_from clo_blk_name i code fv l :
  clo_blk_name ∉ free_variables code ->
  clo_blk_name ∉ fv ->
  subst clo_blk_name l (stores_from i clo_blk_name (tm_store clo_blk_name 0 code) fv) =
  stores_from i l (tm_store l 0 code) fv.
Proof.
  unfold init_clo, stores, stores_from.
  revert code i.
  induction fv; simpl; intros.
  { rewrite subst_not_in //. rewrite decide_True //. }
  { f_equal.
    { case_decide; case_decide; set_solver. }
    rewrite IHfv //. set_solver. }
Qed.

Lemma subst_blk_clo_init clo_blk_name code fv l :
  clo_blk_name ∉ free_variables code ->
  clo_blk_name ∉ fv ->
  subst clo_blk_name l (init_clo clo_blk_name code fv) =
    stores l (tm_store l 0 code) fv.
Proof. apply subst_blk_clo_init_from. Qed.

(****************************************************************)

Lemma substs_store_in (env:list (string * val)) (l:loc) (i:nat) (a:string) :
  NoDup env.*1 ->
  a ∈ env.*1 ->
  substs env (tm_store l i a) =
    tm_store l i (default val_unit ((list_to_map env : gmap string val) !! a)).
Proof.
  intros Hd He.
  induction env as [|(b,v)]; simpl in *; first set_solver.
  inversion Hd; subst. inversion He; subst.
  { rewrite subst_substs_commut //.
    simpl. rewrite decide_True //.
    rewrite lookup_insert //. simpl.
    rewrite substs_free_variables_empty //.
    set_solver. }
  { rewrite IHenv //. simpl.
    f_equal.
    rewrite lookup_insert_ne //.
    set_solver. }
Qed.

Definition stores_from_substs i (env : gmap string val) clo_blk init fv :=
  foldri i
    (fun i binder term =>
       tm_let BAnon
         (tm_store clo_blk (val_nat i) (tm_val (env !!! binder)))
         term)
    init fv.

Lemma stores_from_substs_step i (env:gmap string val) clo_blk init x fv :
  stores_from_substs i env clo_blk init (x::fv) =
    tm_let BAnon (tm_store clo_blk i (tm_val (env !!! x))) (stores_from_substs (S i) env clo_blk init fv).
Proof. easy. Qed.

Lemma substs_store_fromi t env fv i (l:loc) :
  NoDup env.*1 ->
  free_variables t = ∅ ->
  Forall (fun a => a ∈ env.*1) fv ->
  substs env (stores_from i l t fv) =
    stores_from_substs i (list_to_map env) l t fv.
Proof.
  intros ? ? Hfv.
  revert i l.
  unfold stores_from, stores_from_substs.
  induction fv; intros; simpl.
  { rewrite substs_free_variables_empty //. }
  { inversion Hfv. subst.
    rewrite substs_let_anon. f_equal.
    2:{ now apply IHfv. }
    rewrite substs_store_in //. }
Qed.

Lemma locs_substs_stores_from i env init t fv:
  locs (substs env (stores_from i t init fv)) ⊆ locs env.*2 ∪ locs t ∪ locs init.
Proof.
  revert i.
  induction fv as [|x]; unfold stores_from; simpl; intros i.
  { eapply transitivity. apply locs_substs. set_solver. }
  { rewrite substs_let_anon. auto_locs.
    assert (locs (substs env (tm_store t i x)) ⊆ locs t ∪ locs env.*2 ∪ locs_tm init).
    { eapply transitivity. apply locs_substs. auto_locs. set_solver. }
    auto_locs. set_solver. }
Qed.

Lemma locs_substs_store_fromi i env (l:loc) t fv :
  locs (stores_from_substs i (list_to_map env) l t fv) ⊆ {[l]} ∪ locs t ∪ locs env.*2 ∪ locs t.
Proof.
  revert i.
  induction fv as [|x]; unfold stores_from_substs; simpl; intros i.
  { set_solver. }
  { auto_locs.
    assert (locs_val ((list_to_map env : gmap string val) !!! x) ⊆ locs env.*2).
    { auto_locs. clear IHfv. induction env as [|(b,?)]; first set_solver.
      rewrite lookup_total_alt. simpl.
      destruct (decide (x = b)); subst.
      { rewrite lookup_insert. set_solver. }
      { rewrite lookup_insert_ne //. set_solver. } }
    auto_locs. set_solver. }
Qed.

Record correct_up_to (L:list val) (env : gmap string  val) (fv : list string) i :=
  { corr_start : forall j, 1 <= j < i -> L !! j =  Some (env !!! (fv !!! (j - 1)));
    corr_end : forall j, i <= j < length L -> L !! j = Some val_unit}.

Definition soup_mf_from R (env : gmap string val) (fv : list string) lq : iProp Σ :=
  [∗ list] x;q ∈ fv;lq, (env !!! x) ↤?{q} R.

Lemma wp_stores_from_substs prefv prelq lqfv L (l:loc) env v fv i :
  Forall (fun q => q ≠ 0%Qz) lqfv ->
  (* v will be code *)
  is_loc v = false ->
  (* NoDup (List.map fst env) -> *)
  (* i stays within bounds *)
  length prefv = length L - S (length fv) ->
  length fv < length L -> i = S (length prefv) ->
  (* correction *)
  correct_up_to L (list_to_map env) prefv i ->
  l ↦ BBlock L ∗
    soup_mf_from {[+l+]} (list_to_map env) prefv prelq ∗ soup_mf_from ∅ (list_to_map env) fv lqfv -∗
  wp false (stores_from_substs i (list_to_map env) l (tm_store l 0 v) fv)
  (fun _ => soup_mf_from {[+l+]} (list_to_map env) (prefv ++ fv) (prelq ++ lqfv) ∗
    ∃ L', l ↦ BBlock L' ∗
    ⌜length L = length L' /\ L' !! 0 = Some v /\ correct_up_to L' (list_to_map env) (prefv ++ fv) (length L)⌝).
Proof.
  iIntros (Hqlfv ? Hpref Hfvl Hi Hco) "[Hl Hn2]".
  iRevert (prelq lqfv Hqlfv prefv L Hpref Hfvl i Hi Hco) "Hl Hn2".
  iInduction fv as [] "IH"; iIntros (prelq lqfv Hqlfv prefv L Hpref Hfvl i Hi Hco) "Hl [? ?]"; simpl.
  { destruct Hco as [Hc Ht]. simpl in *. replace (length L - 0) with (length L) in Hi by lia. subst.
    iApply (wp_mono with "[Hl]").
    { iApply (@wp_store _ _ _ _ _ 1 ∅); try easy. 2:iFrame. simpl in *. destruct L; simpl in *; try easy.
      destruct v; try easy. }
    simpl. iIntros (?) "(? & ? & _)". iFrame.
    iDestruct (big_sepL2_nil_inv_l with "[$]") as "%HTT". subst.
    rewrite right_id. simpl. iSplitR; try easy.
    iExists _. iFrame. iPureIntro.
    split; last split.
    { rewrite insert_length //. }
    { rewrite list_lookup_insert //. }
    constructor; eauto.
    { intros ?. intros.
      rewrite list_lookup_insert_ne; last lia.
       apply Hc. rewrite Hpref. lia. }
    { intros ?. rewrite insert_length. lia. } }
  rewrite stores_from_substs_step.
  iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%q' [%tl' [%E (Hmfr & ?)]]]". subst.
  inversion Hqlfv.
  iApply @wp_let_nofree.
  iApply (wp_mono with "[Hl Hmfr]").
  iApply (wp_store with "[$]"); try easy; simpl in *; try lia.
  iIntros (?) "(? & ? & ? & _)". simpl.
  iApply (wp_mono with "[-]").
  iApply ("IH" $! (prelq ++ [q']) tl' _ (prefv ++ [a]) with "[%] [%] [%] [%] [$]").
  all: subst; simpl in *.
  1,2,3:rewrite ?insert_length ?app_length; simpl; lia.
  { destruct Hco as [Hc Ht].
    constructor; simpl; eauto; intros j Hj.
    { destruct (decide (j = S (length prefv))).
      { subst. rewrite list_lookup_insert; try lia.
        rewrite lookup_total_app_r; try lia.
        replace (S (length prefv) - 1 - length prefv) with 0 by lia. easy. }
      { rewrite list_lookup_insert_ne //.
        rewrite lookup_total_app_l. 2:lia.
        rewrite Hc //. lia. } }
    { rewrite insert_length in Hj.
      rewrite list_lookup_insert_ne.
      { apply Ht. lia. } lia. } }
  { iFrame. rewrite left_id. iFrame. simpl. easy. }
  { iIntros (_) "(? & [%L' (? & %HL')])". iFrame.
    rewrite insert_length in HL'. destruct HL' as (Hel & ? & HL').
    clear Hco. do 2 rewrite -app_assoc. simpl.
    iFrame. iExists _. iFrame. iPureIntro.
    split; last split; try easy.
    destruct HL' as [Hf Ht]. simpl in *.
    constructor; try easy.
    { intros j Hj. rewrite Hf //.
      rewrite -app_assoc -cons_middle //. } }
  Unshelve. { easy. }
Qed.

Lemma correct_up_to_clo_struct L' v (env:list (string * val)) fv :
  env.*1 = fv ->
  NoDup fv ->
  L' !! 0 = Some v ->
  length L' = S (length fv) ->
  correct_up_to L' (list_to_map env) fv (S (length fv)) ->
  L' = v::env.*2.
Proof.
  intros He Hnd Hv Hl Hc.
  destruct L' as [|v' L']; simpl in *; try easy.
  injection Hv. intros ->. clear Hv.
  f_equal.
  assert (length env = length fv).
  { subst. rewrite fmap_length //. }
  apply list_leibniz. apply list_equiv_lookup.
  intros i.
  destruct Hc as [Hc1 Hc2].
  destruct (decide (i < length fv)).
  { specialize (Hc1 (S i)). simpl in *.
    rewrite Hc1; last lia.
    replace (i-0) with i by lia.
    rewrite -He.
    rewrite list_lookup_total_alt.
    do 2 rewrite list_lookup_fmap.
    destruct (env !! i) eqn:E.
    2:{ apply lookup_ge_None_1 in E. lia. }
    rewrite lookup_total_alt.
    simpl. rewrite (elem_of_list_to_map_1 env p.1 p.2).
    1,2:subst;easy.
    apply (elem_of_list_lookup_2 _ i). rewrite E. f_equal.
    now destruct p. }
  { rewrite lookup_ge_None_2; last lia.
    rewrite lookup_ge_None_2 //. rewrite fmap_length. lia. }
Qed.

Lemma soup_mf_from_weak a v R (env:gmap string val) L lq:
  a ∉ L ->
  soup_mf_from R env L lq -∗
  soup_mf_from R (<[a:=v]> env) L lq.
Proof.
  iIntros (?).
  iRevert (lq).
  iInduction L as [|a'] "IH"; iIntros.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hq".
    subst. easy. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%e [%tl (%E1 & ? & ?)]]".
    subst.
    unfold soup_mf_from. simpl.
    iDestruct ("IH" with "[%] [$]") as "?".
    { set_solver. }
    iFrame.
    destruct (decide (a=a')); subst.
    { set_solver. }
    rewrite lookup_total_insert_ne //. }
Qed.

(* LATER above *)
Lemma soup_mf_from_weak' a v R (env:gmap string val) L lq:
  a ∉ L ->
  soup_mf_from R (<[a:=v]> env) L lq -∗
  soup_mf_from R env L lq.
Proof.
  iIntros (?).
  iRevert (lq).
  iInduction L as [|a'] "IH"; iIntros.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hq".
    subst. easy. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%e [%tl (%E1 & ? & ?)]]".
    subst.
    unfold soup_mf_from. simpl.
    iDestruct ("IH" with "[%] [$]") as "?".
    { set_solver. }
    iFrame.
    destruct (decide (a=a')); subst.
    { set_solver. }
    rewrite lookup_total_insert_ne //. }
Qed.

Lemma right_env_soup R env L lq :
  NoDup env.*1 ->
  env.*1 = L ->
  group_pointedbys R env.*2 lq -∗
  soup_mf_from R (list_to_map env) L lq.
Proof.
  iIntros (He Hr) "Hs".
  iRevert (env He Hr lq) "Hs".
  iInduction L as [] "IH"; iIntros (env He Hr lq) "Hs";
    destruct env; try easy.
  iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%e [%tl (%E1 & ? & ?)]]".
  subst.
  inversion He. subst. destruct p. simpl in *.
  injection Hr. intros ? ->.
  iSpecialize ("IH" with "[% //] [% //] [$]").
  unfold soup_mf_from. simpl.
  rewrite lookup_total_insert. iFrame.
  iApply soup_mf_from_weak; last iFrame.
  set_solver.
Qed.

Lemma right_env_soup' R env L lq :
  NoDup env.*1 ->
  env.*1 = L ->
  soup_mf_from R (list_to_map env) L lq -∗
  group_pointedbys R env.*2 lq .
Proof.
  iIntros (He Hr) "Hs".
  iRevert (env He Hr lq) "Hs".
  iInduction L as [] "IH"; iIntros (env He Hr lq) "Hs";
    destruct env; try easy.
  iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%e [%tl (%E1 & ? & ?)]]".
  inversion He. subst.
  unfold group_pointedbys. simpl in *.
  injection Hr. intros ? ->.
  rewrite lookup_total_insert. iFrame.
  iApply "IH"; eauto.
  iApply soup_mf_from_weak'; last iFrame.
  set_solver.
Qed.

Lemma Forall_in_id {A} (xs : list A) :
  Forall (fun x => x∈xs) xs.
Proof.
  induction xs; try easy.
  constructor.
  { set_solver. }
  eapply Forall_impl; eauto.
  intros. set_solver.
Qed.

Lemma wp_mk_clo_aux env lq self args code :
  self ∉ set_of_args args ->
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  locs code = ∅ ->
  length env = length (fv_clo self args code) ->
  ♢ (1 + length env) ∗ group_pointedbys ∅ env lq -∗
  wp false (substs (zip (fv_clo self args code) env) (mk_clo_aux self args code))
  (fun v => ∃ l, ⌜v = val_loc l⌝ ∗ IsClosureAux env lq self args code l ∗ l ↤ ∅ ∗ Stackable l 1%Qp).
Proof.
  iIntros (? ? Hc Henv) "[Hc Hs1]".

  remember  (zip (fv_clo self args code) env) as env'.

  assert (NoDup env'.*1).
  { subst. rewrite fst_zip; last lia. apply NoDup_elements. }

  unfold mk_clo.

  assert (self ∉ env'.*1).
  { subst. rewrite fst_zip; last lia. set_solver. }
  assert (locs env'.*2 = locs env).
  { subst. rewrite snd_zip; last lia. easy. }

  rewrite substs_let_notin //.

  iApply wp_let_nofree.
  rewrite substs_free_variables_empty //.
  iApply (wp_mono with "[Hc]").
  iApply wp_alloc.
  { rewrite Henv. rew_qz. iFrame. }
  iIntros (v') "[%l [%Hl (Hlp & Hmf & Hc)]]". subst v'.

  simpl.
  rewrite subst_substs_commut //. simpl.
  rewrite subst_blk_clo_init; simpl.
  2,3:set_solver.

  rewrite decide_True //.
  rewrite substs_let_anon.
  rewrite (substs_free_variables_empty _ (val_loc l)).
  2:{ set_solver. }

  iApply wp_let_nofree.
  simpl.

  unfold stores.
  rewrite substs_store_fromi; first last; eauto.
  { subst. rewrite fst_zip; last lia. apply Forall_in_id. }
  { set_solver. }

  iApply (wp_mono with "[-Hmf Hc]").
  iApply (wp_stores_from_substs nil nil lq); try easy.
  4:iFrame.
  1,2:simpl; rewrite replicate_length; lia.
  { constructor; eauto; intros j Hj.
    { lia. }
    { destruct j; simpl; try easy.
      simpl in *.
      rewrite replicate_length in Hj.
      rewrite lookup_replicate. split; simpl in *; try easy; lia. } }
  { iSplitR; try easy.
    { unfold soup_mf_from. simpl. easy. }
    subst.
    iApply right_env_soup; eauto.
    rewrite fst_zip //; last lia.
    rewrite snd_zip //; last lia. }

  iIntros (_) "(? & [%L' (? & %HL')])". simpl.
  destruct HL' as (HlL' & ? & HL').
  simpl in HL'. rewrite replicate_length in HL'.
  iApply wp_val.
  iExists _. iFrame.
  iSplitR; try easy.
  apply correct_up_to_clo_struct with (v:=(code_clo self args code (fv_clo self args code))) in HL'; try easy; first last.
  { rewrite -HlL'. simpl. rewrite replicate_length //. }
  { apply NoDup_elements. }
  { subst. rewrite fst_zip //; last lia. }
  iDestruct (right_env_soup' with "[$]") as "?"; eauto.
  { subst. rewrite fst_zip //; last lia. }
  subst. rewrite snd_zip; last lia.
  iFrame. eauto.
Qed.

Definition IsClosure (env:list (val*Qz)) (self:binder) (args:list binder) (code:tm) (l:loc) : iProp Σ :=
  let self' :=
    match self with
    | BAnon => fresh_string_of_set "self" (free_variables code ∪ set_of_args args)
    | BNamed self => self end in
  IsClosureAux env.*1 env.*2 self' args code l.

Definition correct_name self args :=
  match self with
  | BNamed self => self ∉ set_of_args args
  | BAnon => True end.

Definition fv_clo' self args code :=
  elements (free_variables code ∖ (binder_set self ∪ set_of_args args)).

Lemma fv_clo'_fv_clo args code :
  fv_clo' BAnon args code = fv_clo (fresh_string_of_set "self" (free_variables code ∪ set_of_args args)) args code.
Proof.
  unfold fv_clo, fv_clo'.
  pose proof (fresh_string_of_set_fresh (free_variables code ∪ set_of_args args)) "self".
  unfold binder_set in *. rewrite left_id_L.
  rewrite difference_union_distr_r_L comm_L.
  rewrite subseteq_intersection_1_L //.
  set_solver.
Qed.

Lemma wp_mk_clo env lq self args code :
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  correct_name self args ->
  locs code = ∅ ->
  (* We require the "right" env. *)
  length env = length (fv_clo' self args code) ->
  ♢ (1 + length env) ∗ group_pointedbys ∅ env lq -∗
  wp false (substs (zip (fv_clo' self args code) env) (mk_clo self args code))
  (fun v => ∃ l, ⌜v = val_loc l⌝ ∗ IsClosure (zip env lq) self args code l ∗ l ↤ ∅ ∗ Stackable l 1%Qp).
Proof.
  intros ? ? ? Hr.
  iIntros "(? & ?)".
  iDestruct (big_sepL2_length with "[$]") as "%Hl".
  unfold IsClosure. rewrite fst_zip; last lia. rewrite snd_zip; last lia.
  destruct self; last first; simpl.
  { iApply wp_mk_clo_aux; eauto. iFrame. }
  { pose proof (fresh_string_of_set_fresh (free_variables code ∪ set_of_args args)) "self".
    rewrite fv_clo'_fv_clo.
    iApply wp_mk_clo_aux; eauto.
    { set_solver. }
    { rewrite -fv_clo'_fv_clo //. }
    iFrame. }
Qed.

Lemma subst_list_vals x (v:val) (vals : list val) :
  subst x v <$> (tm_val <$> vals) = (tm_val <$> vals).
Proof.
  induction vals; try easy.
  simpl. f_equal. easy.
Qed.

Lemma subst_clo_name_load clo_name code (l:loc) fv i :
  clo_name ∉ (list_to_set fv : gset string) ->
  subst clo_name l (loads_from i clo_name code fv) =
    (loads_from i l (subst clo_name l code) fv).
Proof.
  intros.
  unfold loads, loads_from. revert i.
  induction fv; simpl; try easy.
  case_decide; intros.
  { set_solver. }
  { case_decide; try easy.
    f_equal. apply IHfv.
    all:set_solver. }
Qed.

Lemma subst_arg_clo x v i (l:loc) code fv :
  x ∉ (list_to_set fv : gset string) ->
  subst x v (loads_from i l code fv) =
    loads_from i l (subst x v code) fv.
Proof.
  unfold loads_from.
  revert i. induction fv; try easy.
  intros. simpl.
  case_decide.
  { set_solver. }
  f_equal. apply IHfv. set_solver.
Qed.

Lemma substs_arg_clo ls i (l:loc) code fv :
  set_of_args ls.*1 ∩ list_to_set fv = ∅ ->
  substs' ls (loads_from i l code fv) =
    loads_from i l (substs' ls code) fv.
Proof.
  induction ls as [|(b,?)]; simpl; try easy.
  intros.
  rewrite IHls. 2:set_solver.
  destruct b; try easy. simpl.
  rewrite subst_arg_clo //.
  unfold set_of_args in *. set_solver.
Qed.

Lemma loads_from_step i cn t x fv :
  loads_from i cn t (x::fv) = tm_let x (tm_load cn i) (loads_from (S i) cn t fv).
Proof. easy. Qed.

Lemma lookup_NoDup_assoc {A B} (env : list (A*B)) x v v' :
  NoDup env.*1 ->
  (x, v) ∈ env ->
  (x, v') ∈ env ->
  v = v'.
Proof.
  intros Hnd Hv Hv'.
  apply elem_of_list_lookup_1 in Hv. destruct Hv as (i,Hv).
  apply elem_of_list_lookup_1 in Hv'. destruct Hv' as (j,Hv').
  destruct (decide (i=j)).
  { subst. rewrite Hv in Hv'. injection Hv'. easy. }
  exfalso. apply n.
  eapply NoDup_lookup; eauto; rewrite list_lookup_fmap.
  { rewrite Hv //. }
  { rewrite Hv' //. }
Qed.

Lemma subset_ok {A} i (fv fv' : list A) :
  (forall j, 0 <= j < length fv -> fv !! j = fv' !! (i+j) ) ->
  fv ⊆ fv'.
Proof.
  intros Hincl e He.
  apply elem_of_list_lookup_1 in He. destruct He as (j,Hj).
  apply (elem_of_list_lookup_2 _ (i+j)).
  rewrite -Hincl //.
  apply lookup_lt_Some in Hj. lia.
Qed.

Lemma locs_loads_from i s c fv :
  locs (loads_from i s c fv) ⊆ locs s ∪ locs c.
Proof.
  unfold loads_from.
  revert i. induction fv; simpl; intros;
  auto_locs; try set_solver.
Qed.

Lemma locs_loads s c fv :
  locs (loads s c fv) ⊆ locs s ∪ locs c.
Proof.
  pose proof (locs_loads_from 1 s c).
  set_solver.
Qed.

Lemma loads_from_clo b i fv env qf self args code (l:loc) t Q :
  env.*1 = fv_clo self args code ->
  NoDup fv ->
  (forall j, 0 <= j < length fv -> fv !! j = (fv_clo self args code) !! (i+j) ) ->
  length fv <= length env ->
  i = length env - length fv ->
  (IsClosureAux env.*2 qf self args code l -∗ wp b (substs env t) Q) -∗
  IsClosureAux env.*2 qf self args code l -∗
  wp b (loads_from (S i) l (substs (take i env) t) fv) Q.
Proof.
  iIntros (Henvfv Hnd Hfv Hlfv Hi) "Hwp Hclo".
  iRevert (i Hi Hfv).
  iInduction fv as [|x fv] "IH"; iIntros (i Hi Hfv).
  { unfold loads_from. subst. simpl.
    replace (length env - 0) with (length env) by lia.
    rewrite firstn_all.
    iSpecialize ("Hwp" with "[$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "Concl". iApply "Concl". }
  rewrite loads_from_step.

  iDestruct "Hclo" as "(Hl & %Hself & %Hc & %Hlenv & ?)".

  iApply wp_let_nofree.
  assert (i < S (length env)).
  { simpl in *. lia. }

  iApply (wp_mono with "[Hl]").
  { iApply wp_load; last iFrame.
    subst. simpl in *. rewrite fmap_length. lia. }
  iIntros (v) "(? & %Hv)".
  simpl in *.
  apply NoDup_cons in Hnd. destruct Hnd as (Hxfv,?).
  rewrite subst_arg_clo; last first.
  { set_solver. }

  replace (subst x v (substs (take i env) t)) with (substs (take (S i) env) t); last first.
  { generalize Hlenv. intros Hlenv'.
    assert (fv_clo self args code !! i = Some x) as Hclox.
    { specialize (Hfv 0). simpl in *.
        rewrite Hfv; last lia.
        replace (i + 0) with i by lia. easy. }

    rewrite subst_substs_commut.
    2:{ intros Hx.
        apply elem_of_list_lookup in Hx. destruct Hx as (j,Hj).
        assert (i ≠ j) as Hne.
        { intros ->.
          assert ((take j env).*1 !! j = None); try congruence.
          rewrite list_lookup_fmap.
          rewrite lookup_take_ge //. }
        apply Hne.
        assert (NoDup (fv_clo self args code)) by apply NoDup_elements.
        eapply NoDup_lookup; eauto.
        rewrite -Henvfv -Hj.
        do 2 rewrite list_lookup_fmap.
        f_equal.
        rewrite lookup_take //.
        destruct (decide (j < i)); try easy.
        { rewrite list_lookup_fmap lookup_take_ge in Hj; last lia.
          simpl in *. congruence. } }

    rewrite (take_S_r env i (x,v)) //.
    { rewrite substs_app //. }
    assert (env.*1 !! i = Some x) as Hv1.
    { rewrite -Hclox Henvfv //. }
    assert (env.*2 !! i = Some v) as Hv2.
    { rewrite Hv. apply list_lookup_lookup_total_lt.
      rewrite fmap_length. lia. }
    rewrite list_lookup_fmap in Hv1. rewrite list_lookup_fmap in Hv2.
    destruct (env !! i) as [(?,?)|]; try easy.
    injection Hv1. injection Hv2. intros. subst. easy. }
  iApply ("IH" with "[% //] [%] [$] [-] [%] [%]").
  1,3:lia.
  { iFrame. eauto. }
  { intros j Hj. specialize (Hfv (S j)). simpl in *.
    rewrite Hfv; last lia.
    f_equal. lia. }
Qed.

Lemma wp_call_clo_aux lq env self args code l vals b Q :
  length args = length vals ->
  IsClosureAux env lq self args code l -∗
  ▷ (IsClosureAux env lq self args code l -∗ wp b (substs (zip (fv_clo self args code) env) (substs' (zip args vals) (subst self l code))) Q) -∗
  wp b (call_clo l (tm_val <$> vals)) Q.
Proof.
  iIntros (Hle) "(Hl & %Hself & %Henv & %Hlocs & Hp) Hwp".

  unfold call_clo.

  iApply (wp_bind_nofree _ (ctx_call1 (val_loc l::vals))).

  iApply (wp_mono with "[Hl]").
  iApply (wp_load with "[$]"). simpl. lia.
  iIntros (v') "[HL %HE]". subst v'.

  iApply (wp_call_later _ _ _ _ (val_loc l::vals)); simpl; eauto.
  { pose proof (locs_loads self code (fv_clo self args code)). set_solver. }

  assert (self ∉ set_of_args (zip args vals).*1).
  { rewrite fst_zip; try lia. easy. }

  rewrite subst_substs'_commut //.
  unfold loads. rewrite subst_clo_name_load.
  2:set_solver.

  rewrite substs_arg_clo.
  2:{ rewrite fst_zip; try lia. set_solver. }

  iAssert (IsClosureAux env lq self args code l) with "[Hp HL]" as "?".
  { iFrame. eauto. }
  iModIntro.

  iApply (loads_from_clo b 0 with "[Hwp]"); try easy; simpl.
  5:{ iIntros. iApply "Hwp". rewrite snd_zip; last lia. iFrame. }
  { rewrite fst_zip //. lia. }
  { apply NoDup_elements. }
  1,2:rewrite zip_with_length; lia.
  rewrite snd_zip; last lia. iFrame.
Qed.

Lemma wp_call_clo_later b env self args code l vals Q :
  length args = length vals ->
  IsClosure env self args code l -∗
  ▷ (IsClosure env self args code l -∗ wp b (substs (zip (fv_clo' self args code) env.*1) (substs' (zip args vals) (subst' self l code))) Q) -∗
  wp b (call_clo l (tm_val <$> vals)) Q.
Proof.
  iIntros (?) "? Hwp".
  iApply (wp_call_clo_aux with "[$]"); eauto.
  iModIntro.
  iIntros "(? & ?)".
  iSpecialize ("Hwp" with "[$]").
  destruct self; simpl; eauto.
  rewrite subst_not_in //.
  { rewrite fv_clo'_fv_clo. iFrame. }
  pose proof (fresh_string_of_set_fresh (free_variables code ∪ set_of_args args)) "self".
  set_solver.
Qed.

Lemma wp_call_clo env self args code l vals b Q :
  length args = length vals ->
  IsClosure env self args code l -∗
  (IsClosure env self args code l -∗ wp b (substs (zip (fv_clo' self args code) env.*1) (substs' (zip args vals) (subst' self l code))) Q) -∗
  wp b (call_clo l (tm_val <$> vals)) Q.
Proof.
  iIntros.
  iApply (wp_call_clo_later with "[$]"); eauto.
Qed.

Lemma closure_aux_free R env lq self args code l :
  l ∉ R ->
  Stackable l 1%Qp ∗ l ↤ ∅ ∗
  IsClosureAux env lq self args code l =[ true | R ]=∗
  ♢ (1 + length env) ∗ group_pointedbys ∅ env lq.
Proof.
  iIntros (?) "(? & ? & (? & ? & %Hlocsl & %Henv & ?))".
  iIntros.
  iMod (interp_free with "[$]") as "(? & ? & ?)"; try easy.
  simpl.
  iMod (group_pointedbys_pred_dealloc with "[$] [$]") as "(? & ?)".
  iModIntro. rew_qz. simpl. iFrame.
Qed.

Lemma closure_free R env self args code l :
  l ∉ R ->
  Stackable l 1%Qp ∗ l ↤ ∅ ∗
    IsClosure env self args code l =[ true | R ]=∗ ♢ (1 + length env) ∗ group_pointedbys ∅ env.*1 env.*2 .
Proof.
  iIntros.
  iDestruct (closure_aux_free with "[$] [$]") as "?"; eauto.
  rewrite fmap_length.
  eauto.
Qed.

End Closure.

(* mk_clo and call_clo are now opaque. *)
Global Opaque mk_clo call_clo.
