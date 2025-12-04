COQC=coqc
USE_NIX ?= false
OUT_DIR ?= _build

ifeq ($(USE_NIX), false)
	COQFLAGS=-R theories LogicalPinning -Q lib/cfml/lib/coq CFML -Q lib/cfml/lib/stdlib CFML.Stdlib -Q lib/tlc/src TLC
else
	COQFLAGS=-R theories LogicalPinning
endif

LIB := theories/Lib
EXM := theories/Examples
LIST_EXM := $(EXM)/Lists
TREE_EXM := $(EXM)/Trees

VFILES_IN_LIB := WPUntyped.v Borrowable.v ValOps.v MRecord.v Stdlib.v
VFILES_LIST_API_NAMES := ListE_API.v ListES_API.v
VFILES_TREE_API_NAMES := Tree_API.v TreeE_API.v TreeS_API.v TreeES_API.v
VFILES_LIST_BARE := List.v ListExec.v
VFILES_LIST_BSTR := List.v
VFILES_TREE_BARE := Tree.v TreeExec.v
VFILES_TREE_BSTR := Tree.v

LIB_VOFILES := $(patsubst %.v,$(LIB)/%.vo,$(VFILES_IN_LIB))
LIST_API_VOFILES := $(patsubst %.v,$(LIST_EXM)/%.vo,$(VFILES_LIST_API_NAMES))
TREE_API_VOFILES := $(patsubst %.v,$(TREE_EXM)/%.vo,$(VFILES_TREE_API_NAMES))
API_VOFILES := $(LIST_API_VOFILES) $(TREE_API_VOFILES)
LIST_BARE_VOFILES := $(patsubst %.v,$(LIST_EXM)/LibBare/%.vo,$(VFILES_LIST_BARE))
LIST_BSTR_VOFILES := $(patsubst %.v,$(LIST_EXM)/LibBStruct/%.vo,$(VFILES_LIST_BSTR))
TREE_BARE_VOFILES := $(patsubst %.v,$(TREE_EXM)/LibBare/%.vo,$(VFILES_TREE_BARE))
TREE_BSTR_VOFILES := $(patsubst %.v,$(TREE_EXM)/LibBStruct/%.vo,$(VFILES_TREE_BSTR))

CFML_DIR := lib/cfml/lib/coq
CFML_VFILES := $(wildcard $(CFML_DIR)/*.v)
CFML_VOFILES := $(CFML_VFILES:.v=.vo)

FILE_PATTERNS = -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob"
define find_rm
	find $(1) \( $(FILE_PATTERNS) \) -delete
endef

.PHONY: default install tlc cfml clean clean-tlc clean-cfml clean-all

default: $(API_VOFILES)

all: cfml default

# Stamp file
INSTALL_DONE := .install_done

default: $(INSTALL_DONE) $(API_VOFILES)
	@echo "[logical-pinning] Compiled all proofs."

install: cfml $(INSTALL_DONE)

$(INSTALL_DONE):
	@echo "[logical-pinning] Installed TLC and CFML"
	@touch $@

tlc:
	@echo "[logical-pinning] Compiling TLC library ... "
	$(MAKE) -C lib/tlc -j4
	@echo "[logical-pinning] Compiled TLC library"

cfml: tlc
	@echo "[logical-pinning] Compiling CFML library ... "
	$(MAKE) -C lib/cfml depend
	$(MAKE) COQEXTRAFLAGS="-Q ../tlc/src TLC" -C lib/cfml -j libcoq stdlib
	@echo "[logical-pinning] Compiled CFML library ... "

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

$(LIB_VOFILES): $(CFML_VOFILES)

$(LIB)/ValOps.vo: $(LIB)/WPUntyped.vo $(LIB)/Borrowable.vo

$(LIB)/MRecord.vo: $(LIB)/WPUntyped.vo $(LIB)/Borrowable.vo $(LIB)/ValOps.vo

$(LIB)/Stdlib.vo: $(filter-out $(LIB)/Stdlib.vo,$(LIB_VOFILES))

# lib: $(LIB_VOFILES)

$(LIST_BARE_VOFILES) $(LIST_BSTR_VOFILES) $(TREE_BARE_VOFILES) $(TREE_BSTR_VOFILES): $(LIB)/Stdlib.vo

$(LIST_EXM)/List_impl.vo: $(LIB)/Stdlib.vo
$(LIST_EXM)/ListE_API.vo: $(LIST_BARE_VOFILES) $(LIST_EXM)/List_impl.vo
$(LIST_EXM)/ListES_API.vo: $(LIST_BSTR_VOFILES) $(LIST_EXM)/List_impl.vo

$(TREE_EXM)/Tree_impl.vo: $(LIB)/Stdlib.vo
$(TREE_EXM)/Tree_API.vo: $(TREE_BARE_VOFILES) $(TREE_EXM)/Tree_impl.vo
$(TREE_EXM)/TreeE_API.vo: $(TREE_BARE_VOFILES) $(TREE_EXM)/Tree_impl.vo
$(TREE_EXM)/TreeS_API.vo: $(TREE_BSTR_VOFILES) $(TREE_EXM)/Tree_impl.vo $(LIST_EXM)/ListE_API.vo
$(TREE_EXM)/TreeES_API.vo: $(TREE_BSTR_VOFILES) $(TREE_EXM)/Tree_impl.vo $(LIST_EXM)/ListE_API.vo

clean:
	$(call find_rm, theories)

clean-tlc:
	$(call find_rm, lib/tlc)

clean-cfml:
	$(call find_rm, lib/cfml)

clean-all: clean clean-tlc clean-cfml
