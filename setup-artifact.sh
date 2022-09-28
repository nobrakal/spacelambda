#!/bin/bash
set -xeu

# This script is intended to be run in a new virtual machine, it has been
# tested with a fresh minimal installation of Ubuntu 20.04 running on a
# VirtualBox with 2048 MB of RAM and 15 GB disk (more than the default), and
# took about 35 minutes.

if
  ! command -v make >/dev/null \
  || ! command -v gcc >/dev/null \
  || ! dpkg -l libgmp-dev
then
	echo "*** Installing make, gcc, libgmp-dev, please type the sudo password ***"
	sudo apt-get -y install make gcc libgmp-dev
else
  echo "Dependencies ok"
fi

if ! command -v opam >/dev/null
then
  echo "*** Installing opam ***"
  sh <(wget -O- https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
else
  echo "Opam available"
fi

echo "*** Running opam init ***"
export OPAMYES=true
opam init --shell-setup --dot-profile="~/.bashrc"
eval $(opam env)

echo "*** Running opam update ***"
opam update

echo "*** Creating new 4.12.0 switch, or switch to 4.12.0 if it exists ***"
opam switch 4.12.0 || opam switch create \
  --repositories=default,coq-released=https://coq.inria.fr/opam/released \
  4.12.0 \
  ocaml-base-compiler.4.12.0

echo "*** Downloading and unzipping project.zip ***"
wget "https://gitlab.inria.fr/fpottier/diamonds/-/archive/master/diamonds-master.tar.gz?path=project" -O project.tar.gz
tar zxvf project.tar.gz --one-top-level=project --strip-components 1
cd project/

echo "*** Ask opam to install dependencies (may take several minutes) ***"
opam install . --deps-only --verbose
eval $(opam env)

echo "*** Compile the project ***"
echo "If an error appears here, try to open a new terminal and run:"
echo "   cd project; make -j2"

make -j2

echo "*** Success ***"
