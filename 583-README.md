# VeLLVM-Exploration
Trying Out VeLLVM for a compilers project

## Build
coq_makefile -f _CoqProject -o CoqMakefile

make -f CoqMakefile

clang -emit-llvm -S -O0 test1.c