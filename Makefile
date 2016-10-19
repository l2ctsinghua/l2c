# Makefile of L2C Compiler

MAJOR_VERSION=0
MINOR_VERSION=9

FLOCQDIR = compcert/flocq

DIRS=compcert/lib compcert/common compcert/ia32 compcert src driver util \
  $(FLOCQDIR)/Core $(FLOCQDIR)/Prop $(FLOCQDIR)/Calc $(FLOCQDIR)/Appli


INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=coqc -q $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(INCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -libs unix,str \
  -I extraction $(INCLUDES)

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq
FLOCQ_CORE=Fcore_float_prop.v Fcore_Zaux.v Fcore_rnd_ne.v Fcore_FTZ.v \
  Fcore_FLT.v Fcore_defs.v Fcore_Raux.v Fcore_ulp.v Fcore_rnd.v Fcore_FLX.v \
  Fcore_FIX.v Fcore_digits.v Fcore_generic_fmt.v Fcore.v
FLOCQ_PROP=Fprop_Sterbenz.v Fprop_mult_error.v Fprop_relative.v \
  Fprop_div_sqrt_error.v Fprop_plus_error.v
FLOCQ_CALC=Fcalc_ops.v Fcalc_bracket.v Fcalc_sqrt.v Fcalc_div.v Fcalc_round.v \
  Fcalc_digits.v
FLOCQ_APPLI=Fappli_rnd_odd.v Fappli_IEEE_bits.v Fappli_IEEE.v
FLOCQ=$(FLOCQ_CORE) $(FLOCQ_PROP) $(FLOCQ_CALC) $(FLOCQ_APPLI)

LIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v UnionFind.v Wfsimpl.v Fappli_IEEE_extra.v

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v Values.v \
  Smallstep.v Behaviors.v Switch.v Determinism.v

ARCH=Archi.v

SEMANTICS=ClightBigstep.v Lint.v Lvalues.v Lenv.v Lsem.v LsemT.v LsemS.v LsemR.v LsemF.v LsemE.v LsemD.v LsemC.v

PROOFS=ExtraList.v Lenvmatch.v MemProof.v LsemTDeterm.v

LV2LS=LustreSGen.v

TOPOSORT=Toposort.v ToposortNodesProof.v ToposortStmtsProof.v Lu2ltProof.v

LS2LR=LustreRGen.v TransTypecmp.v TransMainArgs.v Lt2lsProof.v LustreRGenProof.v TransTypecmpProof.v TransMainArgsProof.v

LR2F=LustreFGen.v OutstructGen.v ClassifyRetsVar.v ResetfuncGen.v SimplEnv.v ClassifyArgsVar.v LustreFGenProof.v OutstructGenProof.v ClassifyRetsVarProof.v ResetfuncGenProof.v SimplEnvProof.v ClassifyArgsVarProof.v

LF2C=CtempGen.v ClightGen.v  CtempProof.v CtempGenProof.v Csem.v ClightGenProof.v

EXTRACTION=extraction.v

LUSTRE2C=Lident.v Ltypes.v Lop.v Lustre.v LustreV.v LustreS.v LustreR.v LustreF.v \
  Cltypes.v Clop.v Ctemp.v Ctypes.v Cop.v Clight.v $(SEMANTICS) $(PROOFS) $(LV2LS) $(TOPOSORT) $(LS2LR) $(LR2F) $(LF2C)

DRIVER=Compiler.v

FILES=$(LIB) $(COMMON) $(ARCH) $(LUSTRE2C) $(DRIVER) $(FLOCQ)
OUTPUT=l2c

all:
	$(MAKE) pre
	$(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) compiler

.PHONY: pre proof extraction compiler test install uninstall clean clean-all

pre:
	@rm -rf Version.ml

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) $*.v

depend: $(FILES)
	@$(COQDEP) $^ > .depend

-include .depend

extraction:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v

Version.ml:
	@echo "let version_msg=\"\\" >$@
	@echo "l2c : Lustre to C semantics preserving compiler." >>$@
	@echo "http://soft.cs.tsinghua.edu.cn/svn/l2c" >>$@
	@echo "Built on: `date +'%Y%m%d %H:%M:%S %z'`" >>$@
	@echo "Built by: `id -un`@`hostname`" >>$@
	@echo "" >>$@
	@echo "\";;" >>$@
	@echo "" >>$@


compiler: Version.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
	&& rm -f $(OUTPUT) && cp _build/driver/Driver.native $(OUTPUT)

compiler-byte: Version.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.native \
	&& rm -f $(OUTPUT).byte && cp _build/driver/Driver.d.native $(OUTPUT).byte

clean: lclean
	rm -f src/*.vo src/*.glob
	rm -fr driver/*.vo driver/*.glob

lclean:
	rm -f *.cmi *.cmo *.out *.luss *.lusst *.lusm *.c $(OUTPUT) Driver.native
	rm -f *.glob *.vo Version.ml
	rm -Rf extraction/*.ml extraction/*.mli _build

clean-all: clean
	rm -f compcert/*.vo compcert/*.glob
	rm -f compcert/common/*.vo compcert/common/*.glob
	rm -f compcert/lib/*.vo compcert/lib/*.glob
	rm -f compcert/ia32/*.vo compcert/ia32/*.glob
	rm -f compcert/flocq/**/*.vo compcert/flocq/**/*.glob
	rm -r test/result
	rm -f .depend

# Install l2c to ~/bin
install: all
	@sh ./util/install.sh

uninstall:
	echo "uninstall ~/bin/l2c"
	rm -rf ~/bin/l2c

# Source Code Statistic
summary:
	@sh ./util/stat.sh
	@sh ./util/checkin.sh

test:
	@sh ./test/test.sh
