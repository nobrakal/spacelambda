# Setup & Build instruction.

This project needs [opam](https://opam.ocaml.org/doc/Install.html) to
install dependencies.
This project uses the [dune](https://dune.build/) build system.

You can run `./setup.sh` to create a local opam switch with correct
dependencies, and build the project.
Please allow at least 20 minutes for the installation and build to
run.

To manually build the project, run `make` or `dune build`.

## Dependencies

| Software  | Version                                  |
|-----------|------------------------------------------|
| OCaml     | 4.13.1                                   |
| Coq       | 8.15.2                                   |
| coq-stdpp | 1.7.0                                    |
| coq-iris  | 3.6.0                                    |
| diaframe  | c84cba84ce7af4da46fe86fb0f3d3dd1e3ed7ba4 |

Please see `setup.sh` for more precise installation instructions of the
dependencies.
