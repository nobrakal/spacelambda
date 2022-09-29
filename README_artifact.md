# Artifact documentation

This is the artifact documentation for the article *A High-Level
Separation Logic for Heap Space under Garbage Collection*. The virtual
machine archive file `artifact.ova` should be provided with this documentation.

The files we refer to in this documentation appear in the virtual machine
	ready to navigate, but can also be browsed online at:

  https://gitlab.inria.fr/amoine/spacelambda


## List of claims

This is a list of the claims that are made in the article, and for each claim,
where to find the corresponding proof.

XXX

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
