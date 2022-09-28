#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

export OPAMYES=true

# Create a local switch. (We assume opam 2 is installed.)

echo "Creating a local switch..."
opam switch create . ocaml-base-compiler.4.13.1
eval "$(opam env --set-switch)"

# Update the package list.

echo "Updating the list of available packages..."
opam update

# Install Coq & deps.

echo "Installing Coq 8.15.2..."
opam install coq.8.15.2

echo "Installing stdpp & Iris"
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stdpp.1.7.0 coq-iris.3.6.0 coq-iris-heap-lang.3.6.0

echo "Installing diaframe"
git clone https://gitlab.mpi-sws.org/iris/diaframe.git diaframe
cd diaframe
git checkout c84cba84ce7af4da46fe86fb0f3d3dd1e3ed7ba4
make real-install
cd ..

echo "Compiling..."
make -j
