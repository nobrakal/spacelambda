#!/bin/bash
set -xeu

# This script is intended to be run in a new virtual machine, it has been
# tested with a fresh minimal installation of Ubuntu 22.04 running on a
# VirtualBox with 2048 MB of RAM and 15 GB disk (more than the default), and
# took about 35 minutes.

echo "*** Installing dependencies, please type the sudo password ***"
sudo apt-get -y install make gcc libgmp-dev git emacs
echo "Dependencies ok"

if ! command -v opam >/dev/null
then
  echo "*** Installing opam ***"
  sh <(wget -O- https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
  opam init
  eval `opam config env`
else
  echo "Opam available"
fi

echo "*** Downloading and unzipping project.tar.gz ***"
wget "https://gitlab.inria.fr/amoine/spacelambda/-/archive/main/spacelambda-main.tar.gz" -O project.tar.gz
tar zxvf project.tar.gz --one-top-level=project --strip-components 1
cd project/

./setup.sh

echo "*** Compile the project ***"
echo "If an error appears here, try to open a new terminal and run:"
echo "   cd project; make -j2"

make -j2

echo "*** Success ***"
