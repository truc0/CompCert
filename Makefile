#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation, either version 2 of the License, or  #
#  (at your option) any later version.  This file is also distributed #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config
include VERSION

BUILDVERSION ?= $(version)
BUILDNR ?= $(buildnr)
TAG ?= $(tag)
BRANCH ?= $(branch)

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS := lib common $(ARCHDIRS) backend cfrontend driver exportclight cparser encode stack elf

COQINCLUDES := $(foreach d, $(DIRS), -R $(d) compcert.$(d))

ifeq ($(LIBRARY_FLOCQ),local)
DIRS += flocq/Core flocq/Prop flocq/Calc flocq/IEEE754
COQINCLUDES += -R flocq Flocq
endif

ifeq ($(LIBRARY_MENHIRLIB),local)
DIRS += MenhirLib
COQINCLUDES += -R MenhirLib MenhirLib
endif

COQCOPTS ?= -w -undeclared-scope
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

ifeq ($(LIBRARY_FLOCQ),local)
FLOCQ=\
  SpecFloatCompat.v \
  Raux.v Zaux.v Defs.v Digits.v Float_prop.v FIX.v FLT.v FLX.v FTZ.v \
  Generic_fmt.v Round_pred.v Round_NE.v Ulp.v Core.v \
  Bracket.v Div.v Operations.v Round.v Sqrt.v \
  Div_sqrt_error.v Mult_error.v Plus_error.v \
  Relative.v Sterbenz.v Round_odd.v Double_rounding.v \
  Binary.v Bits.v
else
FLOCQ=
endif

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Zbits.v Integers.v Archi.v IEEE754_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v \
  Separation.v Builtins0.v Builtins1.v Builtins.v

# Back-end modules (in backend/, $(ARCH)/)

BACKEND=\
  Cminor.v Cminortyping.v Op.v CminorSel.v \
  SelectOp.v SelectDiv.v SplitLong.v SelectLong.v Selection.v \
  SelectOpproof.v SelectDivproof.v SplitLongproof.v \
  SelectLongproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  RTLmach.v RTLmachproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ValueDomain.v ValueAOp.v ValueAnalysis.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSEdomain.v CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  NeedDomain.v NeedOp.v Deadcode.v Deadcodeproof.v \
  Unusedglob.v Unusedglobproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Allocation.v Allocproof.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Debugvar.v Debugvarproof.v \
  Mach.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v AsmFacts.v Asmgenproof.v \
  AsmRegs.v SSAsm.v SSAsmproof.v \
  RealAsm.v RealAsmgen.v RealAsmproof.v \
  UserAsm.v UserAsmFacts.v UserRealAsm.v LocalLib.v \
  PseudoInstructions.v \
  AsmLabelNew.v AsmBuiltinInline.v \
  AsmStructRet.v \
  AsmFloatLiteral.v \
  AsmPseudoInstr.v \
  Asmlabelgen.v \
  PadNops.v \
  PadInitData.v \
  SeqTable.v RelocProgram.v CheckDef.v Symbtablegen.v \
  SymbolString.v Jumptablegen.v \
  SymbtableSort.v \
  Reloctablesgen.v \
  RelocBingen.v \
  RemoveAddend.v \
  SymbtableEncode.v StrtableEncode.v ShstrtableEncode.v ReloctablesEncode.v SymbtableDecode.v TablesEncode.v \
  StrtableDecode.v ShstrtableDecode.v ReloctablesDecode.v RelocBinDecode.v RelocProgSemantics.v RelocProgSemantics1.v RelocProgSemantics2.v RelocProgSemantics3.v RelocElfgen.v

# Encoding of data into bytes

ENCODE=Encode.v Bits.v Hex.v

# 

STACK=Assoc.v

# ELF files
#ELF=RelocElf.v EncodeRelocElf.v RelocElfSemantics.v DecodeRelocElf.v ElfBytesSemantics.v EncodeElfCorrect.v
ELF=RelocElf.v EncodeRelocElf.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v ClightBigstep.v SimplLocals.v SimplLocalsproof.v \
  Cshmgen.v Cshmgenproof.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# Parser

PARSER=Cabs.v Parser.v

# MenhirLib

ifeq ($(LIBRARY_MENHIRLIB),local)
MENHIRLIB=Alphabet.v Automaton.v Grammar.v Interpreter_complete.v \
  Interpreter_correct.v Interpreter.v Main.v Validator_complete.v \
  Validator_safe.v Validator_classes.v
else
MENHIRLIB=
endif

# Putting everything together (in driver/)

DRIVER=Compopts.v Compiler.v Complements.v

# All source files

FILES=$(VLIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(MENHIRLIB) $(PARSER) $(ENCODE) $(STACK) $(ELF)

# Generated source files

GENERATED=\
  $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v $(ARCH)/SelectLong.v \
  backend/SelectDiv.v backend/SplitLong.v \
  cparser/Parser.v

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CLIGHTGEN),true)
	$(MAKE) clightgen
endif
ifeq ($(INSTALL_COQDEV),true)
	$(MAKE) compcert.config
endif

proof: $(FILES:.v=.vo)

# Turn off some warnings for compiling Flocq
flocq/%.vo: COQCOPTS+=-w -compatibility-notation

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

clightgen: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen
clightgen.byte: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	coq2html -d doc/html/ -base compcert -short-names doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)

tools/ndfun: tools/ndfun.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
else
	ocamlc -o tools/ndfun str.cma tools/ndfun.ml
endif

tools/modorder: tools/modorder.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml
else
	ocamlc -o tools/modorder str.cma tools/modorder.ml
endif

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

compcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > compcert.ini

compcert.config: Makefile.config
	(echo "# CompCert configuration parameters"; \
        echo "COMPCERT_ARCH=$(ARCH)"; \
        echo "COMPCERT_MODEL=$(MODEL)"; \
        echo "COMPCERT_ABI=$(ABI)"; \
        echo "COMPCERT_ENDIANNESS=$(ENDIANNESS)"; \
        echo "COMPCERT_BITSIZE=$(BITSIZE)"; \
        echo "COMPCERT_SYSTEM=$(SYSTEM)"; \
        echo "COMPCERT_VERSION=$(BUILDVERSION)"; \
        echo "COMPCERT_BUILDNR=$(BUILDNR)"; \
        echo "COMPCERT_TAG=$(TAG)"; \
        echo "COMPCERT_BRANCH=$(BRANCH)" \
        ) > compcert.config

driver/Version.ml: VERSION
	(echo 'let version = "$(BUILDVERSION)"'; \
         echo 'let buildnr = "$(BUILDNR)"'; \
         echo 'let tag = "$(TAG)"'; \
         echo 'let branch = "$(BRANCH)"') > driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	@rm -f $@
	$(MENHIR) --coq --coq-no-version-check cparser/Parser.vy
	@chmod a-w $@

depend: $(GENERATED) depend1

depend1: $(FILES) exportclight/Clightdefs.v
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 ./ccomp $(DESTDIR)$(BINDIR)
	install -d $(DESTDIR)$(SHAREDIR)
	install -m 0644 ./compcert.ini $(DESTDIR)$(SHAREDIR)
	install -d $(DESTDIR)$(MANDIR)/man1
	install -m 0644 ./doc/ccomp.1 $(DESTDIR)$(MANDIR)/man1
	$(MAKE) -C runtime install
ifeq ($(CLIGHTGEN),true)
	install -m 0755 ./clightgen $(DESTDIR)$(BINDIR)
endif
ifeq ($(INSTALL_COQDEV),true)
	install -d $(DESTDIR)$(COQDEVDIR)
	for d in $(DIRS); do \
          install -d $(DESTDIR)$(COQDEVDIR)/$$d && \
          install -m 0644 $$d/*.vo $(DESTDIR)$(COQDEVDIR)/$$d/; \
	done
	install -m 0644 ./VERSION $(DESTDIR)$(COQDEVDIR)
	install -m 0644 ./compcert.config $(DESTDIR)$(COQDEVDIR)
	@(echo "To use, pass the following to coq_makefile or add the following to _CoqProject:"; echo "-R $(COQDEVDIR) compcert") > $(DESTDIR)$(COQDEVDIR)/README
endif


clean:
	rm -f $(patsubst %, %/*.vo*, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f compcert.ini compcert.config
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

check-proof: $(FILES)
	$(COQCHK) compcert.driver.Complements

print-includes:
	@echo $(COQINCLUDES)

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

-include .depend

FORCE:
