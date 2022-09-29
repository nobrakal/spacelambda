From stdpp Require Import base.
From spacelambda.language Require Import head_semantics gc.

(* ------------------------------------------------------------------------ *)
(* The semantics of SpaceLamba, a reduction interleaving distant steps and gc. *)

(* A "distant" step, maybe below a context *)
Inductive step :
  nat ->
  tm → store →
  tm → store → Prop :=
| StepCtx maxsize t1 σ1 t2 σ2 E t1' t2' :
  t1' = fill_item E t1 ->
  t2' = fill_item E t2 ->
  step maxsize t1 σ1 t2 σ2 ->
  step maxsize t1' σ1 t2' σ2
| StepHead maxsize t1 σ1 t2 σ2 :
  head_step maxsize t1 σ1 t2 σ2 →
  step maxsize t1 σ1 t2 σ2.

Inductive reduction :
  nat ->
  tm -> store -> tm -> store -> Prop :=
| RedStep maxsize t1 σ1 t2 σ2 :
  step maxsize t1 σ1 t2 σ2 ->
  reduction maxsize t1 σ1 t2 σ2
| RedGC maxsize t σ σ' :
  gc (locs t) σ σ' ->
  reduction maxsize t σ t σ'.

(* A curryfied version. *)
Definition reduction' maxsize : relation (tm * store) :=
  fun '(t1,σ1) '(t2,σ2) => reduction maxsize t1 σ1 t2 σ2.
