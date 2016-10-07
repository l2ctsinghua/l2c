#!/bin/bash
#statistic scripts

echo " "
echo "L2C Compiler Source Code Statistic on `date +%Y%m%d`"
echo "* Section 1: Summary "
echo -n "  ** Total lines of coq code               :" 
find . -name '*.v' | xargs grep -v '^$' | wc -l
echo -n "  ** Total lines of ocaml code             : " 
find . -name '*.ml' | xargs grep -v '^$' | wc -l
echo -n "  ***Our developed coq code                :" 
ls ./extraction/*.v src/*.v driver/*.v | xargs grep -v '^$' | wc -l
echo -n "  ***Our developed ml code                 : " 
ls ./driver/*.ml ./src/*.ml compcert/PrintClight.ml | xargs grep -v '^$' | wc -l
echo -n "  ***Total lines from Compcert (*.v code)  :"
find ./compcert/  -name '*.v' | xargs grep -v '^$' | wc -l
echo -n "  ***Total lines from Compcert (*.ml code) :  "
find ./compcert/lib/ ./compcert/common/ ./compcert/flocq/ -name '*.ml' | xargs grep -v '^$' | wc -l

echo " "
echo -n "  ** Total number of l2c definitions       :  "
ls ./extraction/*.v src/*.v driver/*.v | xargs grep -E '(Definition|Fixpoint|Inductive)' | wc -l
echo -n "  ** Total number of l2c lemmas/theorems   :  "
ls ./extraction/*.v src/*.v driver/*.v | xargs grep -E '(Lemma|Theorem)' | wc -l
echo -n "  ** Total number of admitted lemmas       :  "
ls ./extraction/*.v src/*.v driver/*.v | xargs grep -E 'admit' | wc -l

echo " "
echo "* Section 2: Work Breakdown Structure "
echo -n "  ** Lustre syntax and semantics (*.v code): " 
cd src
ls Lustre*.v Lsem*.v Lint.v Lident.v Lvalues.v Lenv*.v Ltypes.v Lop.v Ctemp.v Csem.v | xargs grep -v '^$' | wc -l
echo -n "  *** definitions       :  "
ls Lustre*.v Lsem*.v Lint.v Lident.v Lvalues.v Lenv*.v Ltypes.v Lop.v Ctemp.v Csem.v | xargs grep -E '(Definition|Fixpoint|Inductive)' | wc -l
echo -n "  *** lemmas/theorems   :  "
ls Lustre*.v Lsem*.v Lint.v Lident.v Lvalues.v Lenv*.v Ltypes.v Lop.v Ctemp.v Csem.v | xargs grep -E '(Lemma|Theorem)' | wc -l
echo -n "  *** admitted lemmas   :  "
ls Lustre*.v Lsem*.v Lint.v Lident.v Lvalues.v Lenv*.v Ltypes.v Lop.v Ctemp.v Csem.v | xargs grep -E 'admit' | wc -l

echo -n "  ** Lustre translate (*.v code): " 
ls ../extraction/extraction.v LustreSGen.v Toposort.v LustreRGen.v TransMainArgs.v TransTypecmp.v LustreFGen.v OutstructGen.v ClassifyRetsVar.v ResetfuncGen.v SimplEnv.v ClassifyArgsVar.v CtempGen.v ClightGen.v | xargs grep -v '^$' | wc -l
echo -n "  *** definitions       :  "
ls ../extraction/extraction.v LustreSGen.v Toposort.v LustreRGen.v TransMainArgs.v TransTypecmp.v LustreFGen.v OutstructGen.v ClassifyRetsVar.v ResetfuncGen.v SimplEnv.v ClassifyArgsVar.v CtempGen.v ClightGen.v | xargs grep -E '(Definition|Fixpoint|Inductive)' | wc -l
echo -n "  *** lemmas/theorems   :  "
ls ../extraction/extraction.v LustreSGen.v Toposort.v LustreRGen.v TransMainArgs.v TransTypecmp.v LustreFGen.v OutstructGen.v ClassifyRetsVar.v ResetfuncGen.v SimplEnv.v ClassifyArgsVar.v CtempGen.v ClightGen.v | xargs grep -E '(Lemma|Theorem)' | wc -l
echo -n "  *** admitted lemmas   :  "
ls ../extraction/extraction.v LustreSGen.v Toposort.v LustreRGen.v TransMainArgs.v TransTypecmp.v LustreFGen.v OutstructGen.v ClassifyRetsVar.v ResetfuncGen.v SimplEnv.v ClassifyArgsVar.v CtempGen.v ClightGen.v | xargs grep -E 'admit' | wc -l


echo -n "  ** Lustre translate proof (*.v code): " 
ls *Proof.v ExtraList.v ../driver/Compiler.v | xargs grep -v '^$' | wc -l
echo -n "  *** definitions       :  "
ls *Proof.v ExtraList.v ../driver/Compiler.v | xargs grep -E '(Definition|Fixpoint|Inductive)' | wc -l
echo -n "  *** lemmas/theorems   :  "
ls *Proof.v ExtraList.v ../driver/Compiler.v | xargs grep -E '(Lemma|Theorem)' | wc -l
echo -n "  *** admitted lemmas   :  "
ls *Proof.v ExtraList.v ../driver/Compiler.v | xargs grep -E 'admit' | wc -l

echo -n "  ** Lustre translate (*.ml code): " 
cd ..
cd extraction
ls LustreSGen.ml Toposort.ml LustreRGen.ml TransMainArgs.ml TransTypecmp.ml LustreFGen.ml OutstructGen.ml ClassifyRetsVar.ml ResetfuncGen.ml SimplEnv.ml ClassifyArgsVar.ml CtempGen.ml ClightGen.ml  | xargs grep -v '^$' | wc -l
