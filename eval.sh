#!/bin/sh
# count the lines of code of the Rust compiler
WC="coqwc"
DIR="rustfrontend"
PARSER="rustparser/Rustsurface.ml $DIR/Rustsyntax.v $DIR/Rustlightgen.v"
RL="$DIR/Rusttypes.v $DIR/Rustlight.v $DIR/Rustlightown.v $DIR/InitDomain.v $DIR/RustOp.v $DIR/Rusttyping.v"
RIR="$DIR/RustIR.v $DIR/RustIRown.v $DIR/RustIRsem.v"
IRgen="$DIR/RustIRgen.v $DIR/RustIRgenProof.v"
ELAB="$DIR/RustIRcfg.v $DIR/InitAnalysis.v $DIR/ElaborateDrop.v $DIR/ElaborateDropProof.v"
CLgen="$DIR/Clightgen.v $DIR/Clightgenspec.v $DIR/Clightgenproof.v"
Owncheck="$DIR/MoveChecking.v $DIR/MoveCheckingFootprint.v $DIR/MoveCheckingDomain.v $DIR/MoveCheckingSafe.v"
Safety="common/SmallstepLinkingSafe.v common/InvariantAlgebra.v common/SmallstepSafe.v common/SmallstepClosed.v"
Example="rustdemo/HashMap.v  rustdemo/HashMapCommon.v  rustdemo/HashMapLink.v rustdemo/HashMapSafe.v rustdemo/LinkedList.v     rustdemo/LinkedListSafe.v"

COMP="driver/RA.v driver/CallConvRust.v"

echo "Open Safety, Compositionality and Preservation"
$WC $Safety

echo "Hash Map Example"
$WC $Example

echo "Rustlight"
$WC $RL

echo "RustIR"
$WC $RIR

echo "Parser"
$WC $PARSER

echo "Lowering"
$WC $IRgen

echo "Ownership Checking"
$WC $Owncheck

echo "Drop Elaboration"
$WC $ELAB

echo "Clight Generation"
$WC $CLgen

echo "Simulation Convention"
$WC $COMP

HashMap="rustdemo/*.v"
echo "Running Example"
$WC $HashMap

echo "Owlang Compiler Total"
$WC $RL $RIR $PARSER $IRgen $ELAB $CLgen $COMP

echo "Total"
$WC $Safety $Example $RL $RIR $PARSER $IRgen $Owncheck $ELAB $CLgen $COMP