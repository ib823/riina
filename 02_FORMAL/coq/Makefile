# TERAS Coq Makefile
# Generated for formal proofs

COQMAKEFILE := Makefile.coq

all: $(COQMAKEFILE)
	@+$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $@

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $(COQMAKEFILE) clean
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

check-admits:
	@echo "Checking for Admitted proofs..."
	@grep -r "Admitted\|admit\|todo" *.v */*.v 2>/dev/null && echo "WARNING: Found admits!" || echo "No admits found."

.PHONY: all clean check-admits
