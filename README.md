## SpaceLambda

A Lambda-Calculus with GC, equipped with a Separation Logic.

### Setup & build

This project needs [opam](https://opam.ocaml.org/doc/Install.html) to install dependencies.
You can run `./setup.sh` to create a local opam switch with correct
dependencies, and build the project.
Please allow at least 20 minutes for the installation and build to
run.

To manually build the project, run `make` or `dune build`.

### Architecture

The architecture is as follows:

* `spacelang/` for (almost not modified) files from
  [SpaceLang](https://gitlab.inria.fr/fpottier/diamonds/), taken with
  the authorization of the authors.
* `language/` for the syntax & semantics of the language.
* `examples/` for various examples.
* `fracz/` for an implementation of signed multisets and possibly
  null fractions, with adapted cmras.
* `wps.v`, the front-end of our logic, with a WP with souvenir.
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
* We derive `wp_enc.v`, a wp whose the postcondition is a predicate
  on a particular value (`nat`, `loc`, ...), and not on the type
  `val`.
* We derive `wpc.v`, a wp with a context.
* We derive `wps.v`, which is a `wp` with souvenir.

### Link With Paper

All the development is made with Weakest Preconditions (WP) rather
than triples.
Code pointers are expressed with notation µ λ and application of terms
u and v as (u v).
Closure creation uses the syntax `mk_clo` and closure call the syntax
`call_clo`.
Code pointers must contain no locations. The syntax does not actually
forbid it, so a side-condition locs(t) = ∅ appears from time to time.

|Figure        |File                        |
|--------------|----------------------------|
|2             |`language/syntax.v`         |
|3             |`language/head_semantics.v` |
|4, GC         |`language/gc.v`             |
|4, Red        |`language/semantics.v`      |
|5, 6, 7, 9    |`wps.v`                     |
|8             |`wp_closure.v`              |
|10, rev_append|`examples/list/list_rev.v`  |
|11, 12        |`examples/cps/cps_append.v` |
|11, 13        |`examples/counter/counter.v`|
|14            |`examples/stacks/*.v`       |
|--------------|----------------------------|
|Appendix A.1  |`cloud.v`                   |
|Appendix A.2  |`language/closure.v`        |
|Appendix A.3  |`wp_closure.v`              |
|Appendix A.4  |`wp_spec.v`                 |
|Appendix A.5  |`examples/counter/counter.v`|
|Appendix B.1  |`wps.v`                     |
|15            |`wp.v`                      |
|Appendix B.2  |`language/alt_semantics.v`  |
|Appendix B.4  |`ph.v`                      |
|Appendix B.5  |`interp.v`                  |


|Rule / Definition |File      |Lemma             |
|------------------|----------|------------------|
|Conseq / ConseqGen|`wps.v`   |`wps_conseq`      |
|Frame             |`wps.v`   |`wps_frame`       |
|Cleanup           |`interp.v`|`mapsfrom_cleanup`|
|LogicalFree       |`interp.v`|`logical_free`    |

### ProofGeneral

NB: There is a hack to work with ProofGeneral.
We have a dumb `src/_CoqProject` which make visible the files
produced by dune.

See issue: https://github.com/ProofGeneral/PG/issues/477
