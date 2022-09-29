From stdpp Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.

From spacelambda.spacelang Require Import stdpp hypotheses predecessors.
From spacelambda.fracz Require Import qz smultiset fracset.

(* This file defines how we tie the store σ, the map of predecessors π,
   and a map of additional fracsets μ, through an invariant [tied σ π μ].

   Mainly:
   + The domain of μ is the one of σ
   + All fractions must be negative in μ (therefore all supports are negative)
   + Forall location in both π and μ, its "logical predecessors" from μ must
     be freed.

    The last property allows to generate at will assertions of the form
    [x ↤{0} {[-l-]}] for all freed l.
*)

Section Tied.
Context `{ Hypotheses L B }.

(* A useful notation. *)
Notation dom := (dom (gset L)).

Definition all_neg (μ : gmap L (fracset L)) :=
  map_Forall (fun (_:L) x => frac x = 0%Qz) μ.

Definition freed_intersection (σ:gmap L B) (π:gmap L (gmultiset L)) (μ:gmap L (fracset L)) :=
  map_relation (fun x y => forall i, i ∈ supp y -> freed σ i) (fun _ => True) (fun _ => True) π μ.

Record tied (σ:gmap L B) (π:gmap L (gmultiset L)) (μ:gmap L (fracset L)) :=
  { tied_dom : dom μ = dom σ;
    tied_neg : all_neg μ;
    tied_cov : freed_intersection σ π μ }.

Lemma tied_init :
  tied (∅:gmap L B) ∅ ∅.
Proof.
  constructor; try easy.
  now do 2 rewrite dom_empty_L.
Qed.

Lemma tied_alloc σ π μ l b :
  l ∉ dom σ →
  b <> deallocated ->
  tied σ π μ ->
  tied (<[l:=b]> σ) (<[l:=∅]> π) (<[l:=ε]> μ).
Proof.
  intros ? ? [Hd ? Hcovers].
  constructor.
  { do 2 rewrite dom_insert_L. rewrite Hd. set_solver. }
  { by apply map_Forall_insert_2. }
  { intros i.
    destruct (decide (i=l)); subst.
    { do 2 rewrite lookup_insert. simpl. smultiset_solver. }
    { do 2 rewrite lookup_insert_ne //.
      specialize (Hcovers i). destruct  (π !! i),(μ !! i); try easy. simpl in *.
      intros. apply not_freed_alloc_iff; eauto. } }
Qed.

Lemma tied_dealloc σ π μ l fr :
  l ∈ dom σ ->
  frac fr = 0%Qz ->
  tied σ π μ ->
  tied σ (delete l π) (<[l:=fr]> μ).
Proof.
  intros Hin ? [Hd ? ?]. constructor.
  { rewrite dom_insert_L -Hd. rewrite -Hd in Hin. set_solver. }
  { by apply map_Forall_insert_2. }
  { intros i. destruct (decide (i=l)); subst.
    { by rewrite lookup_delete lookup_insert. }
    { rewrite lookup_delete_ne // lookup_insert_ne //. } }
Qed.

Lemma tied_update σ π μ l gs gs' ns :
  π !! l = Some gs ->
  μ !! l = Some ns ->
  tied σ π μ ->
  tied σ (<[l:=gs']> π) μ.
Proof.
  intros Hπl Hμl [? ? Hcovers]. constructor; eauto.
  intros i.
  specialize (Hcovers i).
   destruct (decide (l = i)); subst.
   { rewrite lookup_insert Hμl.
     rewrite Hπl Hμl in Hcovers. simpl in *. eauto. }
   { rewrite lookup_insert_ne //. }
Qed.

Lemma tied_update_freed σ π μ (l:L) fr (ns:fracset L) :
  l ∈ dom σ ->
  frac fr = 0%Qz ->
  μ !! l = Some ns ->
  (forall i, i ∈ supp fr -> freed σ i \/ i ∈ supp ns) ->
  tied σ π μ ->
  tied σ π (<[l:=fr]> μ).
Proof.
  intros ? ? Hμl Hfr [Hd Hneg Hco]. constructor.
   { rewrite dom_insert_L Hd. set_solver. }
   { now apply map_Forall_insert_2. }
   { intros i. destruct (decide (l = i)); subst.
      { rewrite lookup_insert. destruct (π !! i) eqn:E; try easy.
        simpl. specialize (Hco i). rewrite E Hμl in Hco. simpl in *.
        intros ? Hins. destruct (Hfr _ Hins); eauto. }
      { rewrite lookup_insert_ne //. } }
Qed.

Lemma tied_store_deallocate σ π μ locs :
  tied σ π μ ->
  tied (deallocate locs σ) π μ.
Proof.
  intros [Hd ? Hco]. constructor; try easy.
  { rewrite Hd. apply leibniz_equiv. rewrite dom_deallocate //. }
  { intros i.
    destruct (π !! i) eqn:E1,(μ !! i) eqn:E2; try easy. simpl.
    specialize (Hco i). rewrite E1 E2 in Hco. simpl in *.
    intros. apply freed_deallocate. eauto. }
Qed.

Lemma tied_update_store σ π μ l b b' :
  b ≠ deallocated →
  b' ≠ deallocated →
  tied (<[l:=b]> σ) π μ ->
  tied (<[l:=b']> σ) π μ.
Proof.
  intros ? ? [Hd ? Hco]. constructor; try easy.
  { rewrite Hd. do 2 rewrite dom_insert_L. easy. }
  { intros i.
    destruct (π !! i) eqn:E1,(μ !! i) eqn:E2; try easy. simpl.
    specialize (Hco i). rewrite E1 E2 in Hco. simpl in *.
    intros. eapply not_freed_update_iff.
    3: by apply Hco.
    all:easy. }
Qed.

End Tied.
