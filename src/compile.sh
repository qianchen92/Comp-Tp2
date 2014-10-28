#!/bin/sh
# usage: ./compile.sh <path-to-vsl-source-without-extension>
#
# translating from VSL to LLVM IR (.ll)
./main.native $1.vsl 2>$1.ll
# translating from LLVM IR to LLVM bitcode (.bc)
llvm-as $1.ll
# translating from LLVM bitcode to Assembly code for the local architecture (.s)
llc $1.bc
# call to assembler and linker (through gcc), producing an executable binary
gcc $1.s -o $1
