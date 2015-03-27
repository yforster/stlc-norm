include Makefile.include

#FSTAR_HOME=/opt/FStar
#FSTAR_BIN=fstar.exe
#FSTAR_MONO=mono
#TIMEOUT=100
FSTAR=$(FSTAR_MONO) $(FSTAR_HOME)/bin/$(FSTAR_BIN) --n_cores 1 --max_fuel 1 --max_ifuel 1 --fstar_home $(FSTAR_HOME) --print_implicits

all : stlc-norm

stlc-base : stlc_cbv_db_parsubst.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst stlc_cbv_db_parsubst.fst

stlc-norm : stlc-norm.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst stlc_cbv_db_parsubst.fst stlc-norm.fst

stlc-log : stlc-norm.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst stlc_cbv_db_parsubst.fst stlc-norm.fst --log_types

stlc-lax : stlc-norm.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst stlc_cbv_db_parsubst.fst stlc-norm.fst --lax

stlc-timeout : stlc-norm.fst
	$(FSTAR) --z3timeout $(TIMEOUT) $(FSTAR_HOME)/lib/constr.fst $(FSTAR_HOME)/lib/classical.fst $(FSTAR_HOME)/lib/ext.fst stlc_cbv_db_parsubst.fst stlc-norm.fst

test : test.fst
	$(FSTAR) test.fst

bug : bug.fst
	$(FSTAR) bug.fst
