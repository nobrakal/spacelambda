# Artifact documentation

This is the artifact documentation for the article *A High-Level
Separation Logic for Heap Space under Garbage Collection*. The virtual
machine archive file `artifact.ova` should be provided with this documentation.

The files we refer to in this documentation appear in the virtual machine
	ready to navigate, but can also be browsed online at:

  https://gitlab.inria.fr/amoine/spacelambda

## Generalities

All the development is made with Weakest Preconditions (WP) rather
than triples.

Code pointers are expressed with notation µ λ and application of terms
u and v as (u v).
Closure creation uses the syntax `mk_clo` and closure call the syntax
`call_clo`.

Code pointers must contain no locations. The syntax does not actually
forbid it, so a side-condition locs(t) = ∅ appears from time to time.

### The NoFree mode

Section 5.3 introduces the NoFree mode, a mode where logical
deallocation is forbidden.
While introduced late in the article, this mode appears in the very
definition of the WP, as a boolean parameter.
If the mode is set to `false`, then logical deallocation is forbidden.
Most of our rules are polymorphic in the mode.
Note that a WP expressed with a `false` mode entails the same WP with
any mode (Lemma `wp_nofree` in file `wp.v`).

## List of definitions & claims

This is a list of the definitions & claims that are made in the
article, and where to find the corresponding definition or proof.

* Figure 2 and Section 3.1: In directory `language/`

| Construction         | Definition | File        |
|----------------------|------------|-------------|
| Terms                | `tm`       | `syntax.v`  |
| Values               | `val`      | `syntax.v`  |
| Evaluation Contexts  | `ctx`      | `syntax.v`  |
| Closure construction | `mk_clo`   | `closure.v` |
| Closure call         | `call_clo` | `closure.v` |

* Figure 3 & 4: In directory `language/`

| Relation       | Definition  | File                   |
|----------------|-------------|------------------------|
| Head Reduction | `head_step` | `head_semantics.v`     |
| GC             | `gc`        | `language/gc.v`        |
| Reduction      | `reduction` | `language/semantics.v` |

* Section 4:

| Rule           | Lemma               | File       |
|----------------|---------------------|------------|
| Conseq         | `wp_conseq`         | `wp.v`     |
| Frame          | `wp_frame`          | `wp.v`     |
| LogicalFree    | `logical_free`      | `interp.v` |
| SplitPointedBy | `mapsfrom_split`    | `ph.v`     |
| JoinPointedBy  | `mapsfrom_join`     | `ph.v`     |
| Credits Split  | `diamond_split_iff` | `interp.v` |
| Credits Zero   | `diamond_zero`      | `interp.v` |
| Cleanup        | `mapsfrom_cleanup`  | `interp.v` |

* Figure 5:

| Rule            | Lemma        | File          |
|-----------------|--------------|---------------|
| BinOp           | `wp_bin_op`  | `wp_bin_op.v` |
| IfTrue, IfFalse | `wp_if`      | `wp.v`        |
| Bind            | `wp_bind`    | `wp.v`        |
| LetVal          | `wp_let_val` | `wp.v`        |
| CallPtr         | `wp_call`    | `wp_call.v`   |
| Alloc           | `wp_alloc`   | `wp_alloc.v`  |
| Load            | `wp_load`    | `wp_load.v`   |
| Store           | `wp_store`   | `wp_store.v`  |

* Figure 6 & 7 and Section 5:

Triples with souvenir are first defined in file `wpc.v`.
We incorporate the NoFree mode in file `wps.v`. This file also features the
generalization of lemmas presented in Figure 5 to this new WP.


| Rule               | Lemma                   | File    |
|--------------------|-------------------------|---------|
| BindWithSouvenir   | `wpc_bind`              | `wpc.v` |
| AddSouvenir        | `wpc_context_singleton` | `wpc.v` |
| ForgetSouvenir     | `wpc_weak`              | `wpc.v` |
| BindNoFree         | `wps_bind_nofree`       | `wps.v` |
| ConseqMode         | `wps_conseq`            | `wps.v` |
| ConseqWithSouvenir | `wpc_conseq`            | `wpc.v` |
| UpdateWithSouvenir | `supd_simpl`            | `wp.v`  |

* Theorem 6.1:
  Lemma `wp_adequacy` in file `wp_adequacy.v`.
  We also state the adequacy of the WP with souvenir in Lemma
  `simple_wps_adequacy` in file `wp_adequacy.v`.

* Figure 8 & 9:

| Rule     | Lemma          | File           |
|----------|----------------|----------------|
| MkClo    | `wp_mk_clo`    | `wp_closure.v` |
| CallClo  | `wp_call_clo`  | `wp_closure.v` |
| FreeClo  | `closure_free` | `wp_closure.v` |
| MkSpec   | `wp_mk_spec`   | `wp_spec.v`    |
| CallSpec | `wp_call_spec` | `wp_spec.v`    |
| FreeSpec | `spec_free`    | `wp_spec.v`    |

* Examples on lists: In directory `examples/`.

Our base list definition is more general than the one in the
paper. It is presented in the `ListOf` definition in file `list/list.v`.
We first restrict this definition to the `List` predicate in file `list/list.v`.
We then state and prove the examples of the paper in additional lemmas.

| Claim                                | Formalization                      | File               |
|--------------------------------------|------------------------------------|--------------------|
| List Definition                      | `List_alt`                         | `list/list.v`      |
| Equivalence of `List_alt` and `List` | `List_is_List_alt`                 | `list/list.v`      |
| Preserving spec. of `rev_append`     | `list_rev_append_preserving_spec`  | `list/list_rev.v`  |
| Destructive spec. of `rev_append`    | `list_rev_append_destructive_spec` | `list/list_rev.v`  |
| Definition of `cps_append`           | `cps_append`                       | `cps/cps_append.v` |
| Preserving spec. of `cps_append`     | `cps_append_preserving_spec`       | `cps/cps_append.v` |
| Destructive spec. of `cps_append`    | `cps_append_destructive_spec`      | `cps/cps_append.v` |

* Examples on the counter object: In file `examples/counter/counter.v`

| Claim                     | Formalization        |
|---------------------------|----------------------|
| Definition of `mkcounter` | `mk_counter`         |
| Spec. of `mk_couter`      | `mk_counter_spec'`   |
| Spec of the incr closure  | `counter_call_incr'` |
| Spec of the get closure   | `counter_get_incr'`  |
| Logical deallocation      | `counter_free'`      |

* Examples on stacks: In directory `examples/stack/`

Our base stack definition is more general than the one in the
paper. It is presented in the module `StackOf` in file `stack.v`. We
derive the specifications of the paper by the mean of the `PaperStack`
functor in file `stack.v`

| Claim                      | Formalization       |
|----------------------------|---------------------|
| Spec. of `create`          | `stack_create_spec` |
| Spec. of `push`            | `stack_push_spec`   |
| Spec. of `pop`             | `stack_pop_spec`    |
| Logical deallocation       | `stack_free`        |

We then show three implementations of the `StackOf` module.

| Implementation  | File                |
|-----------------|---------------------|
| Lists           | `stack_list.v`      |
| Arrays          | `stack_chunk.v`     |
| Stack of stacks | `stack_of_stacks.v` |

## Download, installation, sanity-testing

### Option 1: virtual machine

The file `artifact.ova` provided with this documentation can be
imported into VirtualBox 6.1 through File > Import Appliance.
The VM's login and password are both "user", although no login should be required.

Inside the VM, one can open a file e.g. `wp_adequacy.v` by opening a terminal
(Ctrl-Alt-T) and typing `opam exec -- coqide project/src/wp_adequacy.v`.
Replace `coqide` with `emacs` to run Proof General instead.

### Option 2: installation for OPAM users

Reviewers familiar with Coq and OPAM may find it simpler to clone the
following git repository and follow the instructions in file
`INSTALL.md`.

```
https://gitlab.inria.fr/amoine/spacelambda
```

### Option 3: from-scratch installation

We built a script to set up all softwares dependencies in a newly-created VM,
and reviewers experiencing difficulties following `INSTALL.md` and wishing to
avoid downloading the provided VM might try follow the script we used to build
the virtual machine, as it is intended to install everything from scratch,
even though it will modify one's opam existing configuration if any (as
opposed to `INSTALL.md` which creates a local opam directory). In theory one
should only need to run:

```
wget -O- https://gitlab.inria.fr/amoine/spacelambda/-/raw/main/setup-artifact.sh | bash
```

Which should download the project, its dependencies and compile everything.

This script is intended to be run in a new virtual machine, it has been tested
with a fresh minimal installation of Ubuntu Ubuntu 22.04.1 LTS running on a VirtualBox with
2048 MB of RAM and 15 GB disk, and took about 35 minutes.

The script may fail at the very end when the opam environment is out of sync,
in which case one should open a new terminal and run `cd project; make`.


## Evaluation instructions

Reviewers can check that all files compile and that no `Admitted` or `Axiom`
remains. It suffices to open the file `src/axioms.v` and play with it
interactively.
If the Coq command `Print Assumptions xxx` prints "Closed under the
global context" indicates, then `xxx` has no dependencies ([reference](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions)).

One should also open some select `.v` files inside CoqIDE or Proof General and
evaluate the whole file to check that no errors occurs and to verify that the
objects and statements mentioned in the claims are what they are supposed to
be.

## Additional artifact description

We believe the repository is self-contained: the structure of the project, as
well as a link to installation instructions, appear in the `README.md` file of
the repository: `https://gitlab.inria.fr/amoine/spacelambda`
