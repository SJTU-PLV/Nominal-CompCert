#!/bin/sh
# count the lines of code of the Rust compiler
WC="coqwc"
DIR="rustfrontend"
PARSER="rustparser/Rustsurface.ml $DIR/Rustsyntax.v $DIR/Rustlightgen.v"
RL="$DIR/Rusttypes.v $DIR/Rustlight.v $DIR/Rustlightown.v $DIR/InitDomain.v $DIR/RustOp.v"
RIR="$DIR/RustIR.v $DIR/RustIRown.v $DIR/RustIRsem.v"
IRgen="$DIR/RustIRgen.v $DIR/RustIRgenProof.v"
ELAB="$DIR/RustIRcfg.v $DIR/InitAnalysis.v $DIR/ElaborateDrop.v $DIR/ElaborateDropProof.v"
CLgen="$DIR/Clightgen.v $DIR/Clightgenspec.v $DIR/Clightgenproof.v"
COMP="driver/RA.v driver/CallConvRust.v"

echo "Rustlight"
$WC $RL

echo "RustIR"
$WC $RIR

echo "Parser"
$WC $PARSER

echo "RustIRgen"
$WC $IRgen

echo "Drop Elaboration"
$WC $ELAB

echo "Clight Generation"
$WC $CLgen

echo "Simulation Convention"
$WC $COMP

echo "Total"
$WC $RL $RIR $PARSER $IRgen $ELAB $CLgen $COMP