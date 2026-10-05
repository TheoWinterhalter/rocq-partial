# Inspired from https://github.com/palmskog/coq-program-verification-template

# OCaml part: theories/Extract.v extracts to src/extracted.ml{,i}, and
# src/main.ml is the hand-written test driver linked against it.
SRC_DIR  := src
EXE      := $(SRC_DIR)/main.exe
OCAMLOPT ?= ocamlfind ocamlopt
# Compilation order matters: the interface, then the implementation, then the client.
ML_FILES := extracted.mli extracted.ml main.ml

all: rocq ocaml

rocq: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq all

# Build the OCaml executable once the extraction has been (re)generated.
ocaml: rocq
	@+$(MAKE) $(EXE)

$(EXE): $(SRC_DIR)/extracted.mli $(SRC_DIR)/extracted.ml $(SRC_DIR)/main.ml
	cd $(SRC_DIR) && $(OCAMLOPT) $(ML_FILES) -o $(notdir $(EXE))

test: ocaml
	./$(EXE)

clean: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq cleanall
	@rm -f Makefile.rocq Makefile.rocq.conf
	@rm -f $(SRC_DIR)/extracted.ml $(SRC_DIR)/extracted.mli $(EXE)
	@rm -f $(SRC_DIR)/*.cmi $(SRC_DIR)/*.cmx $(SRC_DIR)/*.cmo $(SRC_DIR)/*.o

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

# Without these, the catch-all rule below would try to "build" the sources
# (and fail) by forwarding them to Makefile.rocq.
force _CoqProject Makefile: ;
$(SRC_DIR)/extracted.ml $(SRC_DIR)/extracted.mli $(SRC_DIR)/main.ml: ;

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all rocq ocaml test clean force
