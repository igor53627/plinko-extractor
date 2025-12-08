# Makefile for Plinko State-Syncer Formal Verification

COQC := coqc
COQDEP := coqdep

# Path to RocqOfRust library
ROCQOFRUST_PATH := $(HOME)/pse/paradigm/rocq-of-rust/RocqOfRust

# Flags for our code (specs, simulations, proofs)
COQFLAGS := -Q specs Plinko.Specs -Q sims Plinko.Sims -Q proofs Plinko.Proofs

# Flags for linking layer (needs RocqOfRust + sims + src)
COQFLAGS_LINKING := -R $(ROCQOFRUST_PATH) RocqOfRust -Q sims Plinko.Sims -Q src src -Q linking Plinko.Linking

# Flags for translated code (needs RocqOfRust)
COQFLAGS_TRANS := -R $(ROCQOFRUST_PATH) RocqOfRust -Q src src

# Source files
SPEC_FILES := specs/CommonTypes.v specs/DbSpec.v specs/BinomialSpec.v specs/SwapOrNotSpec.v specs/IprfSpec.v
SIM_FILES := $(wildcard sims/*.v)
PROOF_FILES := $(wildcard proofs/*.v)
TRANS_FILES := $(wildcard src/*.v)
LINKING_FILES := $(wildcard linking/*.v)

ALL_V := $(SPEC_FILES) $(SIM_FILES) $(PROOF_FILES)
ALL_VO := $(ALL_V:.v=.vo)
TRANS_VO := $(TRANS_FILES:.v=.vo)
LINKING_VO := $(LINKING_FILES:.v=.vo)

.PHONY: all clean specs sims proofs linking translate check-deps help ci audit check-admits

all: specs sims proofs

# Build specifications
specs: $(SPEC_FILES:.v=.vo)

# Build simulations (depends on specs)
sims: specs $(SIM_FILES:.v=.vo)

# Build proofs (depends on sims)
proofs: sims $(PROOF_FILES:.v=.vo)

# Build translated Rust code (requires RocqOfRust library)
translation: $(TRANS_VO)

# Build linking layer (requires RocqOfRust + sims + translation)
linking: sims translation $(LINKING_VO)

# Compile spec .v to .vo
specs/%.vo: specs/%.v
	$(COQC) $(COQFLAGS) $<

# Compile sims .v to .vo
sims/%.vo: sims/%.v
	$(COQC) $(COQFLAGS) $<

# Compile proofs .v to .vo
proofs/%.vo: proofs/%.v
	$(COQC) $(COQFLAGS) $<

# Compile translated .v to .vo
src/%.vo: src/%.v
	@if [ -d "$(ROCQOFRUST_PATH)" ]; then \
		$(COQC) $(COQFLAGS_TRANS) $<; \
	else \
		echo "Error: RocqOfRust not found at $(ROCQOFRUST_PATH)"; \
		echo "Build it first: cd rocq-of-rust/RocqOfRust && make"; \
		exit 1; \
	fi

# Compile linking .v to .vo
linking/%.vo: linking/%.v
	@if [ -d "$(ROCQOFRUST_PATH)" ]; then \
		$(COQC) $(COQFLAGS_LINKING) $<; \
	else \
		echo "Error: RocqOfRust not found at $(ROCQOFRUST_PATH)"; \
		echo "Build it first: cd rocq-of-rust/RocqOfRust && make"; \
		exit 1; \
	fi

# Explicit dependencies for specs
specs/DbSpec.vo: specs/CommonTypes.vo
specs/BinomialSpec.vo: specs/CommonTypes.vo
specs/SwapOrNotSpec.vo: specs/CommonTypes.vo
specs/IprfSpec.vo: specs/CommonTypes.vo specs/BinomialSpec.vo

# Explicit dependencies for proofs
proofs/DbProofs.vo: specs/DbSpec.vo specs/CommonTypes.vo
proofs/SwapOrNotProofs.vo: specs/SwapOrNotSpec.vo
proofs/IprfProofs.vo: specs/IprfSpec.vo specs/SwapOrNotSpec.vo specs/BinomialSpec.vo
proofs/PrpBridge.vo: proofs/SwapOrNotProofs.vo specs/SwapOrNotSpec.vo
proofs/IprfConcrete.vo: proofs/PrpBridge.vo proofs/IprfProofs.vo specs/IprfSpec.vo

# Explicit dependencies for sims
sims/SimTypes.vo: specs/CommonTypes.vo

# Generate dependencies
depend:
	$(COQDEP) $(COQFLAGS) $(ALL_V) > .depend

# Translate Rust to Rocq using rocq-of-rust
translate:
	@echo "Translating Plinko Rust code to Rocq..."
	cd ../.. && cargo +nightly-2024-12-07 rocq-of-rust
	@echo "Translation complete. Check src/ for generated .v files."

# Clean generated files
clean:
	rm -f specs/*.vo specs/*.glob specs/*.vok specs/*.vos
	rm -f sims/*.vo sims/*.glob sims/*.vok sims/*.vos
	rm -f proofs/*.vo proofs/*.glob proofs/*.vok proofs/*.vos
	rm -f src/*.vo src/*.glob src/*.vok src/*.vos
	rm -f linking/*.vo linking/*.glob linking/*.vok linking/*.vos
	rm -f .depend

# Check if dependencies are installed
check-deps:
	@which $(COQC) > /dev/null || (echo "Error: coqc not found. Install Rocq first." && exit 1)
	@echo "Rocq version: $$($(COQC) --version)"
	@if [ -d "$(ROCQOFRUST_PATH)" ]; then \
		echo "RocqOfRust: $(ROCQOFRUST_PATH)"; \
		if [ -f "$(ROCQOFRUST_PATH)/M.vo" ]; then \
			echo "RocqOfRust library: compiled"; \
		else \
			echo "RocqOfRust library: NOT compiled (run 'make' in RocqOfRust/)"; \
		fi \
	else \
		echo "RocqOfRust: NOT FOUND"; \
	fi

# CI target
ci: clean all linking
	@echo "CI build complete!"

# Audit axioms and admits
audit:
	@echo "=== Plinko Axiom/Admit Audit ==="
	@echo ""
	@echo "Axiom declarations:"
	@grep -rn '^Axiom' specs/ sims/ proofs/ linking/ 2>/dev/null || echo "  (none)"
	@echo ""
	@echo "Parameter declarations:"
	@grep -rn '^Parameter' specs/ sims/ proofs/ linking/ 2>/dev/null || echo "  (none)"
	@echo ""
	@echo "Admits:"
	@grep -rni '\badmitted\b' specs/ sims/ proofs/ linking/ 2>/dev/null || echo "  (none)"

# Threshold for allowed admits
ADMIT_THRESHOLD ?= 10

# Check admits don't exceed threshold
check-admits:
	@echo "Checking admit count against threshold ($(ADMIT_THRESHOLD))..."
	@ADMITS=$$(grep -rni '\badmitted\b' proofs/ linking/ 2>/dev/null | wc -l | tr -d ' '); \
	if [ "$$ADMITS" -gt "$(ADMIT_THRESHOLD)" ]; then \
		echo "ERROR: admit count ($$ADMITS) exceeds threshold ($(ADMIT_THRESHOLD))"; \
		exit 1; \
	else \
		echo "OK: admit count ($$ADMITS) within threshold ($(ADMIT_THRESHOLD))"; \
	fi

# Help
help:
	@echo "Plinko State-Syncer Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all         - Build specs, sims, and proofs (default)"
	@echo "  specs       - Build specification files"
	@echo "  sims        - Build simulation files"
	@echo "  proofs      - Build proof files"
	@echo "  translation - Build translated Rust code (requires RocqOfRust)"
	@echo "  translate   - Re-translate Rust to Rocq (requires rocq-of-rust)"
	@echo "  linking     - Build linking layer (requires RocqOfRust)"
	@echo "  clean       - Remove all generated files"
	@echo "  check-deps  - Verify dependencies are installed"
	@echo "  ci          - CI build (clean + all + linking)"
	@echo "  audit       - List axioms, parameters, and admits"
	@echo "  check-admits- Fail if admits exceed threshold"
	@echo "  help        - Show this message"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - Rocq 9.x (opam switch rocq-9)"
	@echo "  - RocqOfRust library (for 'translation' and 'linking' targets)"

-include .depend
