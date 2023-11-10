rm /workspaces/VeLLVM-Exploration/CoqMakefile
rm /workspaces/VeLLVM-Exploration/CoqMakefile.conf

rm /workspaces/VeLLVM-Exploration/src/.*.aux
rm /workspaces/VeLLVM-Exploration/src/*.glob
rm /workspaces/VeLLVM-Exploration/src/*.vo
rm /workspaces/VeLLVM-Exploration/src/*.vok
rm /workspaces/VeLLVM-Exploration/src/*.vos

#rm /workspaces/VeLLVM-Exploration/CoqMakefile.d

coq_makefile -f _CoqProject -o CoqMakefile

make -f CoqMakefile
