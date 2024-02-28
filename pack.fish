#!/usr/bin/env fish
rm -rf proofs proofs.zip
mkdir proofs
mkdir proofs/beta
mkdir proofs/eta
cp beta/{*.v, *.sig, Makefile} proofs/beta
cp eta/{*.v, *.sig, Makefile} proofs/eta
cp README.md proofs
zip -r proofs.zip proofs
