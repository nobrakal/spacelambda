# SpaceLambda

A Lambda-Calculus with GC, equipped with a Separation Logic.

## Setup & build

See [INSTALL.md](https://gitlab.inria.fr/amoine/spacelambda/-/blob/main/INSTALL.md).

## Architecture

The architecture is as follows:

* `spacelang/` for (almost not modified) files from
  [SpaceLang](https://gitlab.inria.fr/fpottier/diamonds/), taken with
  the authorization of the authors.
* `language/` for the syntax & semantics of the language.
* `examples/` for various examples.
* `fracz/` for an implementation of signed multisets and possibly
  null fractions, with adapted cmras.
* `wps.v`, the front-end of our logic, with a wp with souvenir.
  1. The NoFree mode is a souvenir `None`.
  2. Otherwise a souvenir is with `Some R`.
* The soundness is stated in `wp_adequacy.v`

Internally:
* `wp.v` for the base wp.
* `ph.v` for the ghost state of points-to & pointed-by assertions.
* `interp.v` for the state interpretation.
* `wp_alloc.v`, `wp_call.v`, `wp_closure.v`, `wp_spec.v`, `wp_load.v`,
  `wp_nat_op.v`, `wp_store.v` for the specification of
  primitive operations.
* Based on `wp.v`, we derive `wp_enc.v`, a wp whose the postcondition is a predicate
  on a particular value (`nat`, `loc`, ...), and not on the type
  `val`.
* Based on `wp_enc.v`, we derive `wpc.v`, a wp with a context.
* Based on `wpc.v`, we derive `wps.v`, which is a wp with souvenir.

Even more internally:
* `more_maps_and_sets.v` describes additional lemmas on maps and sets.
* `more_space_lang.v` defines the extension of pointed-by
  assertions to values, following SpaceLang.
* `cloud.v` proves lemmas to logically deallocate cycles.
* `tied.v` describes the links between various logical heaps.
* `triple.v` defines a sugar for Separation Logic triples.
* `utils.v` defines the iterated star over various constructions.

## ProofGeneral

NB: There is a hack to work with ProofGeneral.
We have a dumb `src/_CoqProject` which make visible the files
produced by dune.

See issue: https://github.com/ProofGeneral/PG/issues/477
