From iris.proofmode Require Import proofmode.
From spacelambda.spacelang Require Import stdpp.
From spacelambda.spacelang Require Export hypotheses.

(* ------------------------------------------------------------------------ *)

Class RHypotheses `{Hypotheses L B} := {
  (* We assume that certain blocks can be recognized as stack cells.
     The pointers stored in these blocks are the roots. *)
  is_stack_cell: B → Prop;

  decision_is_stack_cell: ∀b, Decision (is_stack_cell b);

  (* A stack cell is not deallocated. *)
  stack_cell_not_deallocated:
    ~ is_stack_cell deallocated;

  (* The default inhabitant of the type [block] is not a stack cell.
     This hypothesis is not absolutely necessary, but this allows to
     prove the lemma [is_root_reformulation] in successors.v without
     requiring [r ∈ dom s]. *)
  inhabitant_not_stack_cell:
    ~ is_stack_cell inhabitant;
}.
