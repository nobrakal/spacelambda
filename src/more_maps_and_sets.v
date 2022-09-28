From stdpp Require Import sets gmap.

Section Misc.
  Context {A:Type}.

  Lemma union_with_None_l (y:option A) :
    union_with (fun x _ => Some x) None y = y.
  Proof.
    unfold union_with.
    by destruct y; simpl.
  Qed.

  Lemma union_with_Some_l (x:A) (y:option A) :
    union_with (fun x _ => Some x) (Some x) y = Some x.
  Proof.
    unfold union_with.
    by destruct y; simpl.
  Qed.
End Misc.

Section More_gset.

Context `{Countable A}.
Context `{EqDecision A}.

Lemma difference_union (X Y : gset A) :
  X ∪ Y = (X ∖ Y) ∪ Y.
Proof.
  apply leibniz_equiv.
  split; intros.
  { destruct (decide (x ∈ Y)); set_solver. }
  { set_solver. }
Qed.

End More_gset.

Section More_gmap.

  Context `{Countable K}.
  Context `{A:Type}.

  Implicit Type X : gmap K A.

  Lemma gmap_equiv_singleton `{Equiv A} (k:K) (v1 v2:A):
    v1 ≡ v2 -> {[k:=v1]} ≡@{gmap K A} {[k:=v2]}.
  Proof.
    intros. intros i.
    destruct (decide (k=i)) as [->|].
    - do 2 rewrite lookup_singleton. now constructor.
    - do 2 (rewrite lookup_singleton_ne; try easy).
      now constructor.
  Qed.

  Lemma dom_map_union_with_full (f:A → A → option A) X Y :
    (forall x y, is_Some (f x y)) ->
    dom (gset K) (union_with f X Y) = dom (gset K) X ∪ dom (gset K) Y.
  Proof.
    intros Hf.
    apply leibniz_equiv.
    split; intros E.
    { apply elem_of_dom in E.
      destruct E as (y,E).
      apply lookup_union_with_Some in E.
      destruct E as [(E&?)|[(E&?)|E]].
      { apply elem_of_union_l. by apply elem_of_dom. }
      { apply elem_of_union_r. by apply elem_of_dom. }
      { apply elem_of_union_l.
        destruct E as (?,(?,(?&?))).
        by apply elem_of_dom. } }
    { apply elem_of_union in E.
      apply elem_of_dom.
      rewrite lookup_union_with.
      destruct E as [E|E]; apply elem_of_dom in E; destruct E as (q,Hq).
      all:destruct (X !! x); destruct (Y !! x); try easy;
        injection Hq; intros ->.
      all:by apply Hf. }
  Qed.

  Definition restrict X (d:gset K) :=
    filter (fun '(x,_) => x ∈ d) X.

  Lemma lookup_restrict X d x :
    restrict X d !! x = if (decide (x ∈ d)) then X !! x else None.
  Proof.
    unfold restrict.
    rewrite map_filter_lookup.
    destruct (X !! x); try easy.
    simpl. by destruct (decide (x ∈ d)).
  Qed.

  Lemma dom_restrict X d :
    dom (gset K) (restrict X d) = dom (gset K) X ∩ d.
  Proof.
    apply leibniz_equiv. unfold restrict.
    rewrite dom_filter; try easy.
    intros ?.
    rewrite elem_of_intersection.
    split.
    { intros [E ?].
      apply elem_of_dom in E. destruct E as (?,?).
      by eexists. }
    { intros [? []].
      split; try easy.
      apply elem_of_dom.
      by eexists. }
  Qed.

End More_gmap.

From iris.algebra Require Import cmra gmap.

Section More_gmap_cmra.

  Context `{Countable K}.
  Context `{A:cmra}.

  Lemma prove_gmap_valid (m:gmap K A) :
    (forall i x, m !! i = Some x -> ✓ x) -> ✓ m.
  Proof.
    intros Hv i.
    destruct (m !! i) eqn:E; try easy.
    eapply Hv, E.
  Qed.

  Lemma lookup_union_singleton (m1 m2:gmap K A) (k:K) (v:A) :
      {[ k := v ]} ≼ (m1 ∪ m2) ->
      {[ k := v ]} ≼ m1 \/ {[ k := v ]} ≼ m2.
  Proof.
    intros Hincl.
    apply singleton_included_l in Hincl.
    destruct Hincl as (y,(He&?)).
    apply Some_equiv_eq in He.
    destruct He as (y',(He&Hequiv)).
    apply lookup_union_Some_raw in He.
    destruct He as [He|(?&He)]; [left|right]; apply singleton_included_l;
      exists y'; now rewrite He Hequiv.
  Qed.

End More_gmap_cmra.
