## Language

Here are the syntax & semantics of SpaceLambda.

* `syntax.v` defines the syntax.
* `head_semantics.v` defines the `head_step` relation. That is, a
  small-step of reduction, unaware of the GC & evaluation contexts.
* `semantics.v` defines the `reduction` relation. It allows a
  `head_step` under a context, with a GC before.
* `semantics_alt.v` defines an alternative semantics `alt_reduction`,
  used inside the WP definition.

The `reduction` and `alt_reduction` are equivalent, see `semantics_equivalence.v`.
