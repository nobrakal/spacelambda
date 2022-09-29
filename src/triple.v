From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From spacelambda.spacelang Require Import successors predecessors.
From spacelambda.language Require Import language notation.
From spacelambda.fracz Require Import qz qz_cmra.
From spacelambda Require Import ph wp interp.

From spacelambda Require Export wps.

Definition triple `{interpGS Σ} `{Enc A} (r:option (gset loc)) (H:iProp Σ) (t:tm) (Q:A -> iProp Σ) : Prop :=
  (H ⊢ wps r t Q)%I.

Declare Scope triple_scope.
Open Scope triple_scope.

Notation "'CODE' t 'SOUV' r 'PRE' H 'POST' Q" :=
  (triple (Some r) H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODE'  t  '/' 'SOUV'  r  '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.

Notation "'CODE' t 'PRE' H 'POST' Q" :=
  (triple (Some ∅) H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODE'  t  '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.

Notation "'CODEFF' t 'PRE' H 'POST' Q" :=
  (triple None H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODEFF'  t  '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.
