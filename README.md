# VeLLVM-Exploration
Trying Out VeLLVM for a compilers project

# For Instructors
    All relevant code is under src/demo
    - exactEqBlocks.v: This is the first part of the demo. It demonstrates basic/syntactic Itree bisimilarity.
    - bisimilarInstructions.v: This is the second part of the demo. It demonstrates bisimilarity of interpreted instructions.
    - transformPipelineEx.v: This is the final part of the demo. It demonstrates a series of "assembly transformations" 
                                and the correctness of these transformations by bisimulation on a concrete program.

## Build
coq_makefile -f _CoqProject -o CoqMakefile

make -f CoqMakefile

# Notes to self
## Directories
/workspaces/VeLLVM-Exploration/
/home/coq/vellvm/
/home/coq/InteractionTrees

### How to get VIR from a C program

#### From C to LLVM
clang -emit-llvm -S -O0 <filename>.c

#### From LLVM to VIR internal ast
/home/coq/vellvm/src/vellvm --print-ast sanity.ll

#### Ast to VIR 
-Past into coq and remove metadata
-do annoying fixes like quote strings and change "n%Z" to "n%N"
- Do dumb transformation in df_instrs. (x:xs) to (x , xs)