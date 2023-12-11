# VeLLVM-Exploration
Trying Out VeLLVM for a compilers project

## Build
coq_makefile -f _CoqProject -o CoqMakefile

make -f CoqMakefile


# Directories
/workspaces/VeLLVM-Exploration/
/home/coq/vellvm/
/home/coq/InteractionTrees

## How to get VIR from a C program

#### From C to LLVM
clang -emit-llvm -S -O0 <filename>.c

#### From LLVM to VIR internal ast
/home/coq/vellvm/src/vellvm --print-ast sanity.ll

#### Ast to VIR 
-Past into coq and remove metadata
-do annoying fixes like quote strings and change "n%Z" to "n%N"
- Do dumb transformation in df_instrs. (x:xs) to (x , xs)