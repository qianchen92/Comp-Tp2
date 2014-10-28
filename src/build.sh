#!/bin/sh
#ocamlbuild -cflags -I,+llvm -lflags -I,+llvm ./main.native
ocamlbuild -use-ocamlfind ./main.native
