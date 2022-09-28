From stdpp Require Import binders gmultiset.
From iris.algebra Require Import gmap auth.

From iris.proofmode Require Import coq_tactics tactics reduction spec_patterns intro_patterns.

From glaneur.fracz Require Import qz smultiset.
From glaneur.language Require Import notation closure.
From glaneur Require Import interp triple.

From glaneur Require Import wpc more_space_lang wp_all.
From glaneur Require Import wp_spec wpc.

From glaneur.examples Require Export diaframe.

(******************************************************************************)
(* LNE *)

Ltac lne_pre tt :=
  match goal with
  | |- LNE ?r => unfold r
  | |- LNE (?r _) => unfold r
  | |- LNE (?r _ _) => unfold r
  | |- LNE (?r _ _ _) => unfold r
  | |- LNE (?r _ _ _ _) => unfold r
  | |- LNE (?r _ _ _ _ _) => unfold r
  | |- LNE (?r _ _ _ _ _ _) => unfold r
  | |- LNE (?r _ _ _ _ _ _ _) => unfold r
  | _ => fail "Not a LNE goal, or with too many arguments" end.

Ltac lne :=
  lne_pre tt;
  intros ? ? ? ? ? ? ?;
    repeat f_equiv; eauto.

(******************************************************************************)
(* Force rew *)

Ltac force_rew_post_core tt :=
  first [ rewrite post_unit
        | rewrite post_nat
        | rewrite post_loc
        | rewrite post_val ].
Ltac force_rew_post :=
  repeat (force_rew_post_core tt).


(******************************************************************************)
(* Rewriting maps *)
Ltac rew_dom_step tt :=
  first [ rewrite dom_singleton_L
        | rewrite dom_op
        | rew_map_set_step tt ].

Ltac rew_dom_core tt :=
  repeat (rew_dom_step tt).

Tactic Notation "rew_dom" := rew_dom_core tt.

(******************************************************************************)
(* Extending the context. *)

Ltac wps_context l :=
  lazymatch type of l with
  | loc =>
      iApply (@wps_context_singleton _ _ l)
  | val =>
      iApply (@wps_context_vsingleton _ _ l) end;
  first (rew_set; iFrame).

(******************************************************************************)
(* Vals & if *)

Ltac wps_val :=
  do 2 iStepS.

Ltac wps_if :=
  iApply wps_if.

(******************************************************************************)
(* Call *)

Ltac wps_call := do 3 iStepS.

Ltac wps_call_spec E :=
  iApply (@wps_call_spec_tac);
  [ try easy | try easy | ]; try (iFrame; try iIntros (?) E) .

Tactic Notation "wps_call_spec" "as" constr(E) := wps_call_spec E.
Tactic Notation "wps_call_spec" := wps_call_spec "?".

(******************************************************************************)
(* Free *)

Ltac wps_free l Hpost :=
  iApply (@wps_free_singleton _ _ l with "[$]");
  [ try set_solver | rew_dom; try set_solver | iIntros Hpost ].

Tactic Notation "wps_free" ident(l) "as" constr(Hpost) :=
  wps_free l Hpost.
Tactic Notation "wps_free" ident(l) :=
  wps_free l as "[? ?]".

(******************************************************************************)
(* wp_load. *)

Ltac wps_load := do 5 iStepS.

(******************************************************************************)
(* mine some diamonds. *)

Ltac fetch_diamonds Δ k :=
  lazymatch Δ with
  | context[Esnoc _ ?Hdiams (♢ ?c)%I] => k Hdiams c
  | _ =>
      fail "wp_alloc: could not find any space credits in hypothesis" end.

Ltac mine_aux n Hdst Hdiams c :=
  let xs := intro_pat.parse Hdst in
  replace (c:Qz) with ((c-n)%Qz + n%Qz)%Qz;
  [ iDestruct (diamonds_split with "[$]") as [IList [ IIdent Hdiams::xs ] ]; rew_qz; simpl |
    rew_qz; simpl; try easy; try lia ].

Ltac mine n Hdst :=
  lazymatch goal with
  | |- envs_entails ?Δ _ =>
      let mine' := mine_aux n Hdst in
      fetch_diamonds Δ mine' end.

Tactic Notation "mine" constr(n) "as" constr(ipat) :=
  mine n ipat.
Tactic Notation "mine" constr(n) :=
  mine n as "?".

Lemma diamonds_eq `{!interpGS Σ} d1 d2 :
  d1 = d2 ->
  ♢ d1 -∗ ♢ d2.
Proof. intros ->. easy. Qed.

Ltac conclude_diamonds :=
  repeat (iDestruct (diamonds_join with "[$]") as "?");
  simpl;
  iApply (diamonds_eq with "[$]");
  rew_qz; try lia; try easy.

(******************************************************************************)
(* wp_alloc. *)
(* LATER use mine *)

Ltac wps_mono H :=
  lazymatch goal with
  | |- envs_entails ?Δ (wps _ _ ?Q) =>
  lazymatch type of Q with
  | val -> _ => (* We apply of stronger lemma in case of val *)
      iApply (@wps_mono_val with H)
  | _ =>
      iApply (@wps_mono with H) end end.

Ltac fetch_diamonds' Δ :=
  lazymatch Δ with
  | context[Esnoc _ ?Hdiams (♢ _)%I] => Hdiams
  | _ =>
      fail "wp_alloc: could not find any space credits in hypothesis" end.

Ltac wps_alloc l Hpost :=
  lazymatch goal with
  | |- envs_entails ?Δ (wps _ (tm_alloc (tm_val (val_nat ?n))) ?Q) =>
    let Hdiams := fetch_diamonds' Δ in
    wps_mono [SGoal (SpecGoal GSpatial false [] [Hdiams] false)] ;
    (* Apply the lemma [wp_alloc_split] with the hypotheses [Hdiams]. *)
    [ iApply (wps_alloc_split with "[$]");
      try (rew_qz; lia)
    | iIntros (l) Hpost
    ] end.

Tactic Notation "wps_alloc" ident(l) "as" constr(Hpost) :=
  wps_alloc l Hpost; rewrite ?post_val ?enc_loc.
Tactic Notation "wps_alloc" ident(l) :=
  wps_alloc l as "(?&?&?)"; rewrite ?post_val ?enc_loc.
Tactic Notation "wps_alloc" :=
  let l := fresh "l" in
  wps_alloc l; rewrite ?post_val ?enc_loc.

(******************************************************************************)
(* wp_store. *)

Ltac wps_store := (* LATER repeat until goal looks like ok *)
  do 6 iStepS;
  lazymatch goal with
  | |- envs_entails ?Δ (wps _ _ _) => idtac
  | |- envs_entails ?Δ _ => do 2 iStepS end.

(******************************************************************************)
(* wps_apply *)

(* First two lemmas, depending on the post, for enc. *)
Lemma wps_apply `{interpGS Σ} `{Enc A} r r' t (Q Q': A -> iProp Σ) P :
  r' ⊆ r ->
  (P -∗ wps (Some r') t Q') -∗
  P ∗ (∀ v, Q' v -∗ Q v)%I -∗
  wps (Some r) t Q.
Proof.
  iIntros (?) "Hwp (? & Hc)".
  iApply @wps_weak; eauto.
  iSpecialize ("Hwp" with "[$]").
  iApply (@wps_mono with "[$]").
  iIntros.
  iApply ("Hc" with "[$]").
Qed.

Lemma wps_apply_val `{interpGS Σ} `{Enc A} r r' t (Q: val -> iProp Σ) (Q':A -> iProp Σ) P :
  r' ⊆ r ->
  (P -∗ wps (Some r') t Q') -∗
  P ∗ (∀ v, Q' v -∗ Q (enc v))%I -∗
  wps (Some r) t Q.
Proof.
  iIntros (?) "Hwp (? & Hc)".
  iApply @wps_weak; eauto.
  iSpecialize ("Hwp" with "[$]").
  iApply (@wps_mono_val with "[$]").
  iIntros.
  iApply ("Hc" with "[$]").
Qed.

Ltac wps_apply_aux wps_apply spec l Hpost tac :=
  iApply wps_apply;
  [ |iApply spec|]; last iFrame; first (tac tt);
  last (try iFrame; try iIntros (l) Hpost); rew_enc.

Ltac wps_nofree :=
  iApply wps_nofree.

Lemma wps_apply' `{interpGS Σ} (A:Type) (EA:Enc A) t (Q Q': A -> iProp Σ) P :
  (P -∗ wps None t Q') -∗
  P ∗ (∀ v, Q' v -∗ Q v)%I -∗
  wps None t Q.
Proof.
  iIntros "Hwp (? & Hc)".
  iSpecialize ("Hwp" with "[$]").
  iApply (@wps_mono with "[$]").
  iIntros.
  iApply ("Hc" with "[$]").
Qed.

Lemma wps_apply_val' `{interpGS Σ} (A:Type) (EA:Enc A) t (Q: val -> iProp Σ) (Q':A -> iProp Σ) P :
  (P -∗ wps None t Q') -∗
  P ∗ (∀ v, Q' v -∗ Q (enc v))%I -∗
  wps None t Q.
Proof.
  iIntros "Hwp (? & Hc)".
  iSpecialize ("Hwp" with "[$]").
  iApply (@wps_mono_val with "[$]").
  iIntros.
  iApply ("Hc" with "[$]").
Qed.

Ltac wps_apply_aux' wps_apply spec l Hpost :=
  iApply wps_apply;
  [iApply spec|]; last iFrame;
  last (try iFrame; try iIntros (l) Hpost); rew_enc.

Ltac wps_apply spec l Hpost tac :=
  lazymatch goal with
  | |- envs_entails ?Δ (wps (Some _) _ ?Q) =>
  lazymatch type of Q with
  | val -> _ =>
      wps_apply_aux @wps_apply_val spec l Hpost tac
  | _ =>
      wps_apply_aux @wps_apply spec l Hpost tac end
  | |- envs_entails ?Δ (wps None _ ?Q) =>
  lazymatch type of Q with
  | val -> _ =>
      wps_apply_aux' @wps_apply_val' spec l Hpost
  | _ =>
      wps_apply_aux' @wps_apply' spec l Hpost end end.

Ltac set_solver' tt := set_solver.

Tactic Notation "wps_apply" constr(H) "as" "(" simple_intropattern(l) ")" constr(Hpost) "by" tactic(tac) :=
  wps_apply H (l) Hpost tac.
Tactic Notation "wps_apply" constr(H) "as" "(" simple_intropattern(l) ")" constr(Hpost) :=
  wps_apply H as (l) Hpost by set_solver'.
Tactic Notation "wps_apply" constr(H) "as"  constr(Hpost) :=
  wps_apply H as (?) Hpost by set_solver'.
Tactic Notation "wps_apply" constr(H) := wps_apply H as (?) "?".

(******************************************************************************)
(* wps_bin_op *)

Ltac wps_bin_op := do 3 iStepS.

(******************************************************************************)
(* Simplify terms with trailing substs *)

Ltac simplify_subst tt :=
  match goal with
  | |- context G [subst ?x ?v ?t] =>
      let b := eval vm_compute in (bool_decide (x ∉ free_variables t)) in
        match b with
        | true => rewrite (subst_not_in x v t); last (by vm_compute)
        | _ => fail end end.

Ltac simplify_substs tt :=
  repeat (rewrite subst_call_clo);
  simpl;
  repeat (simplify_subst tt).

Tactic Notation "simplify_substs" := simplify_substs tt.

(******************************************************************************)
(******************************************************************************)
(* Bind *)

(******************************************************************************)
(* [1] Specialized lemmas *)

(* A tactic lemma, which tries to reduce computation, using an intermediate evar *)
Lemma wps_let_tac `{Enc A} `{!interpGS Σ} lt2 r (x:binder) t1 t2 k (Q:A -> iProp Σ) :
  lt2 = locs t2 ->
  lt2 ⊆ r ∪ (dom k) ->
  Stackables k  -∗
  wps (Some (r ∪ lt2)) t1 (fun v => Stackables k -∗ wps (Some r) (subst' x v t2) Q) -∗
  wps (Some r) (tm_let x t1 t2) Q.
Proof.
  intros -> ?. iIntros.
  iApply (wps_let with "[$]"); try easy.
Qed.

Lemma wps_let_tac_vnotctxs `{Enc A} `{!interpGS Σ} lt2 v qp r x t1 t2 k (Q:A -> iProp Σ) :
  lt2 = locs t2 ->
  lt2 ⊆ r ∪ (dom k) ∪ locs_val v ->
  Stackables k -∗ vStackable v qp -∗
  wps (Some (r ∪ lt2)) t1 (fun w => Stackables k -∗ vStackable v qp -∗ wps (Some r) (subst' x w t2) Q) -∗
  wps (Some r) (tm_let x t1 t2) Q.
Proof.
  intros -> ?. iIntros "Hc Hwpc ?".
  destruct (is_loc v) eqn:E.
  { destruct v; try easy. simpl.
    iDestruct (Stackables_union with "[$]") as "?".
    iApply (wps_let with "[$]"); try easy.
    { rewrite dom_op dom_singleton. set_solver. }
    iApply (wps_mono with "[$]").
    iIntros (?) "Hp ? ".
    iDestruct (Stackables_split with "[$]") as "(? & ?)".
    iApply ("Hp" with "[$] [$]"). }
  { iApply (wps_let_tac with "[$]"). easy.
    destruct v; simpl in *; set_solver.
    iApply (wps_mono with "[$]").
    iIntros (?) "Hp". iIntros.
    iApply ("Hp" with "[$] [$]"). }
Qed.

(* A specialized lemma when there is no need for Stackables. *)
Lemma wps_let_empty `{!Enc A} `{!interpGS Σ} lt2 r x t1 t2 (Q:A -> iProp Σ) :
  lt2 = locs t2 ->
  lt2 ⊆ r ->
  wps (Some r) t1 (fun v => wps (Some r) (subst' x v t2) Q) -∗
  wps (Some r) (tm_let x t1 t2) Q.
Proof.
  intros -> ?.
  iIntros "Hwpc".
  iApply wps_bupd.
  iMod Stackables_empty as "Hnctx".
  iApply (wps_mono with "[Hwpc Hnctx]").
  { iApply (wps_let with "[$]").
    { set_solver. }
    iApply (wps_mono with "[-]").
    { iApply (wps_weak with "[$]").
      set_solver. }
    iIntros (?) "? _".
    iFrame. }
  eauto.
Qed.

(* A tactic lemma, with only one vStackable *)
Lemma wps_let_tac_vnotctx `{Enc A} `{!interpGS Σ} lt2 v qp r x t1 t2 (Q:A -> iProp Σ) :
  lt2 = locs t2 ->
  lt2 ⊆ r ∪ locs_val v ->
  vStackable v qp -∗
  wps (Some (r ∪ lt2)) t1 (fun w => vStackable v qp -∗ wps (Some r) (subst' x w t2) Q) -∗
  wps (Some r) (tm_let x t1 t2) Q.
Proof.
  intros -> ?. iIntros "Hc Hwpc".
  destruct (is_loc v) eqn:E.
  { destruct v; try easy. simpl.
    iApply (wps_let with "[$]"); try easy.
    rewrite dom_singleton. set_solver. }
  { iApply wps_let_empty.  easy.
    destruct v; simpl in *; set_solver.
    assert ((r ∪ locs t2) = r) as -> by (destruct v; simpl in *; set_solver).
    iApply (wps_mono with "[$]").
    iIntros (?) "Hp".
    iApply ("Hp" with "[$]"). }
Qed.

(******************************************************************************)
(* [2] To rewrite locs *)

Lemma locs_no_loc x :
  is_loc x = false ->
  locs_val x = ∅.
Proof.
  intros. destruct x; try easy.
Qed.

Ltac wps_bind_empty tac :=
  iApply (@wps_let_empty);
  [ simpl_locs; reflexivity | try tac | rew_set ; simpl subst'; simpl subst ].

Ltac wps_bind_nonempty tac Hctx :=
  iApply (@wps_let_tac with Hctx);
  [ simpl_locs; reflexivity | | repeat (iDestruct (Stackables_union with "[$]") as "?"); iFrame | ]; (* Two levels because of evar solving *)
  [ rew_dom; try tac | rew_set ; simpl subst'; simpl subst ].

Ltac wps_bind_nonempty_vnotctxs tac Hctx :=
  iApply (@wps_let_tac_vnotctxs with Hctx);
  [ simpl_locs; reflexivity | | repeat (iDestruct (Stackables_union with "[$]") as "?"); iFrame | iFrame | ]; (* Two levels because of evar solving *)
  [ rew_dom; try tac | rew_set ; simpl subst'; simpl subst ].

Ltac wps_bind_nonempty_vnotctx tac Hctx :=
  iApply (@wps_let_tac_vnotctx with Hctx);
  [ simpl_locs; reflexivity | | iFrame | ]; (* Two levels because of evar solving *)
  [ rew_dom; try tac | rew_set ; simpl subst'; simpl subst ].

(******************************************************************************)
(* [3] Ltac2 Magic to do a set-minus using only syntactic equality *)

From Ltac2 Require Import Ltac2.

(* This parse a term e as a union of singletons *)
Ltac2 rec parse_unions_aux (acc : constr list) e : constr list :=
  match! e with
  | union ?e1 ?e2 =>
      let acc' := parse_unions_aux acc e1 in
      let acc'' := parse_unions_aux acc' e2 in
      acc''
  | singleton ?l => constr:(val_loc $l)::acc
  | locs_val ?v => v::acc
  | _ => acc end.
Ltac2 parse_unions e := parse_unions_aux [] e.

Ltac2 remove_dup (l:constr list) : constr list :=
  List.nodup Constr.equal l.

Ltac2 set_minus left (right : constr list) :=
  List.filter_out (fun x => List.mem Constr.equal x right) left.

(* of_list *)
Ltac2 constr_of_list nil (xs:constr list) : constr :=
  let cons x y := constr:($x::$y) in
  List.fold_right cons nil xs.

Ltac2 compute_needed_locs (locs:constr) (ctx:constr) :=
  set_minus (remove_dup (parse_unions locs)) (parse_unions ctx).

Ltac2 to_constr_go x :=
  match Ltac1.to_constr x with
  | Some x => x
  | None => Control.throw_invalid_argument "to_constr_go" end.

Ltac2 rec to_list xs :=
  match! xs with
  | nil => []
  | ?x::?xs => x::(to_list xs)
  | _ => Message.print (Message.of_constr xs); Control.throw_invalid_argument "to_list" end.

Ltac2 rec split_list xs :=
  match xs with
  | [] => ([],[])
  | x::xs =>
      let (le,ri) := split_list xs in
      match! x with
      | val_loc ?l => (l::le, ri)
      | _ => (le,x::ri) end end.

(* The main function. Assuming
   + locs : list val
   + ctx : gset loc
   + cont : ltac "of type" list loc -> list val -> ()

   It computes the difference between locs and the location easily found in ctx.
   It gives the result to cont. *)
Ltac2 compute_needed_and_pre (vals:Ltac1.t) (ctx:Ltac1.t) (cont:Ltac1.t) :=
  let locs := to_list (to_constr_go vals) in
  let ctx := to_constr_go ctx in
  let needed := set_minus (remove_dup locs) (parse_unions ctx) in
  let (locs,vals) := split_list needed in
  let lt1 := constr_of_list constr:(@nil loc) locs in
  let vl1 := constr_of_list constr:(@nil val) vals in
  Ltac1.apply cont [Ltac1.of_constr lt1; Ltac1.of_constr vl1] (fun cont => Ltac1.run cont).

(* Ltac1 encapsulation *)
Ltac compute_needed_and_use vals ctx cont :=
  let f := ltac2:(x1 x2 x3 |- compute_needed_and_pre x1 x2 x3) in
  f vals ctx cont.

(******************************************************************************)
(* [4] Tactics to gather and bind the right hypotheses. *)

(* Fetch a "Stackable" hypothesis from the context Δ *)
Ltac fetch_Stackable Δ v :=
  lazymatch v with
  | ?l =>
      lazymatch Δ with
      | context[Esnoc _ ?H (Stackable l ?q)%I] => H
      | context[Esnoc _ ?H (Stackables {[l := ?q]})%I] => H
      | context[Esnoc _ ?H (own γctx (auth.auth_frag {[l := ?q]}))] => H
      | _ => fail "Could not find Stackable" l "in context" Δ end
  | _ => fail "Could not find context information about" v
  end.

Ltac fetch_vStackable Δ v :=
  lazymatch Δ with
  | context[Esnoc _ ?H (vStackable v ?q)%I] => H
  | _ => fail "Could not find vStackable" v "in context" Δ
  end.

(* map fetch on a list *)
Ltac map_fetch Δ xs :=
  match xs with
  | nil => constr:(@nil ident)
  | ?x::?xs =>
      let y := fetch_Stackable Δ x in
      let ys := map_fetch Δ xs in
      constr:(y::ys) end.

(* Given a context Δ, a tactic tac and a list of locs,
   gather the locations from the context, and bind them *)
Ltac gather_and_bind Δ tac locs vals :=
  match locs with
  | nil =>
      lazymatch vals with
      | nil => wps_bind_empty tac
      | cons ?v nil =>
          let vctx := fetch_vStackable Δ v in
          let Hctx :=
            constr:([SGoal (SpecGoal GSpatial false [] [vctx] false)]) in
          wps_bind_nonempty_vnotctx tac Hctx
      | _ => fail "cannot handle two vnotctx: " vals end
  | _  =>
      let ys := map_fetch Δ locs in
      let Hctx := constr:([SGoal (SpecGoal GSpatial false [] ys false)]) in
      lazymatch vals with
      | nil => wps_bind_nonempty tac Hctx
      | cons ?v nil =>
          let vctx := fetch_vStackable Δ v in
          let Hctx' :=
            constr:(Hctx ++ [SGoal (SpecGoal GSpatial false [] [vctx] false)]) in
          let Hctx'' := eval cbn in Hctx' in
          wps_bind_nonempty_vnotctxs tac Hctx''
      | _ => fail "cannot handle two vnotctx" vals end end.

(******************************************************************************)
(* [5] Alternative to locs, llocs, which compute the list of locations in a
   term *)

(* Actually, we compute a list of list of locations, and keep only what looks
   like a singleton using ltac.

   This allows to throw away locations of opaque values *)

(* Compute effectively the list of locs in a term. *)
Fixpoint llocs_tm_aux acc (t:tm) : list (list loc) :=
  match t with
  | tm_var _ => acc
  | tm_val v => val_pointer_list v ::acc
  (* We consider only closed functions *)
  | tm_call _ xs => List.fold_left llocs_tm_aux xs acc
  | tm_alloc t1 => llocs_tm_aux acc t1
  | tm_let _ t1 t2 | tm_bin_op _ t1 t2 | tm_load t1 t2 =>
    llocs_tm_aux (llocs_tm_aux acc t1) t2
  | tm_if t1 t2 t3 | tm_store t1 t2 t3 =>
    llocs_tm_aux (llocs_tm_aux (llocs_tm_aux acc t1) t2) t3
  end.
Definition llocs_tm (t:tm) : list (list loc) := llocs_tm_aux nil t.

(* We remove everything that do not looks like a singleton *)
Ltac filter_non_singletons xs :=
  lazymatch xs with
  | nil => constr:(@nil val)
  | ?x::?xs =>
      let ys := filter_non_singletons xs in
      match x with
      | (val_pointer_list ?v) => constr:(v::ys)
      | ?l::nil => constr:(val_loc l::ys)
      | _ => ys end
  | llocs_tm_aux ?acc _ => (* If llocs_tm failed to progress, keep only the accumulator *)
      let tmp := eval cbn in acc in
        filter_non_singletons acc
  | llocs_tm _ => constr:(@nil val)
  end.

(******************************************************************************)
(* [6] Finally, the main tactic *)

(* LATER we compute 2 times the list of locs. Compute lcos only one time, and remove llocs... *)

(* tac is applied to the side-goal requiring to prove that we gave all the
   needed Stackables *)
Ltac wps_bind tac :=
  auto_locs_goal;
  lazymatch goal with
  | |- envs_entails ?Δ (wps ?r (tm_let _ ?t1 ?t2) ?Q) =>
      lazymatch r with
      | None => iApply wps_let_nofree
      | Some ?r =>
      let gather_and_bind := gather_and_bind Δ tac in
      let lt2 := fresh "llocs" in
      pose (lt2 := llocs_tm t2);
      (* LATER use autorewrite. *)
      repeat (cbn in lt2; rewrite ?call_clo_eq ?mk_clo_eq in lt2);
      lazymatch goal with
      | lt2 := ?lt2c |- _ =>
        let lt2' := filter_non_singletons lt2c in
        clear lt2;
        compute_needed_and_use lt2' r gather_and_bind end end end.

Tactic Notation "wps_bind" "by" tactic(tac) :=
  wps_bind tac.
Tactic Notation "wps_bind" :=
  wps_bind ltac:(set_solver).

Ltac wps_bind_nofree := iApply wps_let_nofree.
