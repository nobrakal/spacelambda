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

## List of definitions & claims

This is a list of the definitions & claims that are made in the
article, and for each claim, where to find the corresponding proof.

* Figure 2: `language/syntax.v`
* Figure 3: `language/head_semantics.v`
* Figure 4:
  + GC relation: `language/gc.v`
  + reduction relation: `language/semantics.v`
* Section 4.1:
  + Rule Conseq: Lemma `wp_conseq` in `wp.v`
  + Rule Frame: Lemma `wp_frame` in `wp.v`
* Section 4.2:
  + Rule LogicalFree: Lemma `logical_free` in `interp.v`
* Section 4.3:
  + Rule SplitPointedBy: Lemma `mapsfrom_split` in `ph.v`
  + Rule JoinPointedBy: Lemma `mapsfrom_join` in `ph.v`
* Figure 5:
  + Rule BinOp: Lemma `wp_bin_op` in `wp_bin_op.v`
  + Rules IfTrue, IfFalse: Lemma `wp_if` in `wp.v`
  + Rule Bind: Lemma `wp_bind` in `wp.v`
  + Rule LetVal: Lemma `wp_let_val` in `wp.v`
  + Rule CallPtr: Lemma `wp_call` in `wp_call.v`
  + Rule Alloc: Lemma `wp_alloc` in `wp_alloc.v`
  + Rule Load: Lemma `wp_load` in `wp_load.v`
  + Rule Store: Lemma `wp_store` in `wp_store.v`
* Section 4.6:
  + Rule Cleanup: Lemma `mapsfrom_cleanup` in `interp.v`
* Figure 6:
  + Rule BindWithSouvenir: Lemma `wpc_bind` in `wpc.v`
  + Rule AddSouvenir: Lemma `wpc_context_singleton` in `wpc.v`
  + Rule ForgetSouvenir: Lemma `wpc_weak` in `wpc.v`
* Figure 7:
  + Rule BindNoFree: Lemma `wps_bind_nofree` in `wps.v`
  + Rule ConseqMode: Lemma `wps_conseq` in `wps.v`
* Section 5.2:
  + Rule ConseqWithSouvenir: Lemma `wpc_conseq` in `wpc.v`
  + Rule UpdateWithSouvenir: Lemma `supd_simpl` in `wp.v`
* Theorem 6.1:
  Lemma `wp_adequacy` in `wp_adequacy.v`
* Figure 8:
  + Rule MkClo: Lemma `wp_mk_clo` in `wp_closure.v`
  + Rule CallClo: Lemma `wp_call_clo` in `wp_closure.v`
  + Rule FreeClo: Lemma `closure_free` in `wp_closure.v`
* Figure 9:
  + Rule MkSpec: Lemma `wp_mk_spec` in `wp_spec.v`
  + Rule CallClo: Lemma `wp_call_spec` in `wp_spec.v`
  + Rule FreeClo: Lemma `spec_free` in `wp_spec.v`


## Download, installation, sanity-testing

### Option 1: virtual machine

The file `artifact.ova` provided with this documentation can be
imported into VirtualBox 6.1 through File > Import Appliance.
The VM's login and password are both "user", although no login should be required.

Inside the VM, one can open file e.g. `wp_adequacy.v` by opening a terminal
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

XXX

## Additional artifact description

We believe the repository is self-contained: the structure of the project, as
well as a link to installation instructions, appear in the `README.md` file of
the `project` directory of the repository:
`https://gitlab.inria.fr/amoine/spacelambda`
