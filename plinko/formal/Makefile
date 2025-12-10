# Makefile for Plinko Formal Verification

# Rocq 9.x uses 'rocq compile' instead of 'coqc'
# Fall back to coqc/coqdep for compatibility with older versions
COQC ?= $(shell command -v rocq >/dev/null 2>&1 && echo "rocq compile" || echo "coqc")
COQDEP ?= $(shell command -v rocq >/dev/null 2>&1 && echo "rocq dep" || echo "coqdep")

# Path to RocqOfRust library (can be overridden via environment or command line)
ROCQOFRUST_PATH ?= $(HOME)/rocq-of-rust/RocqOfRust

# Flags for our code (specs, simulations, proofs)
COQFLAGS := -Q specs Plinko.Specs -Q sims Plinko.Sims -Q proofs Plinko.Proofs

# Flags for linking layer (needs RocqOfRust + sims + src)
COQFLAGS_LINKING := -R $(ROCQOFRUST_PATH) RocqOfRust -Q sims Plinko.Sims -Q src src -Q linking Plinko.Linking

# Flags for translated code (needs RocqOfRust)
COQFLAGS_TRANS := -R $(ROCQOFRUST_PATH) RocqOfRust -Q src src

# Source files
SPEC_FILES := specs/CommonTypes.v specs/DbSpec.v specs/BinomialSpec.v specs/TrueBinomialSpec.v specs/SwapOrNotSpec.v specs/IprfSpec.v
SIM_FILES := $(wildcard sims/*.v)
PROOF_FILES := $(wildcard proofs/*.v)
TRANS_FILES := $(wildcard src/*.v)
LINKING_FILES := $(wildcard linking/*.v)

ALL_V := $(SPEC_FILES) $(SIM_FILES) $(PROOF_FILES)
ALL_VO := $(ALL_V:.v=.vo)
TRANS_VO := $(TRANS_FILES:.v=.vo)
LINKING_VO := $(LINKING_FILES:.v=.vo)

.PHONY: all clean specs sims proofs linking translate check-deps help ci ci-quick ci-full audit check-admits admit-count verify-axioms

all: specs sims proofs

# Artifacts directory for CI
ARTIFACTS_DIR ?= artifacts

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
specs/TrueBinomialSpec.vo: specs/CommonTypes.vo
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
sims/SwapOrNotSim.vo: specs/CommonTypes.vo specs/SwapOrNotSpec.vo sims/SimTypes.vo proofs/SwapOrNotProofs.vo
sims/IprfSim.vo: sims/SimTypes.vo specs/IprfSpec.vo specs/CommonTypes.vo
sims/HintInitSim.vo: sims/SimTypes.vo sims/IprfSim.vo specs/IprfSpec.vo specs/CommonTypes.vo

# Explicit dependencies for linking
linking/types.vo: specs/CommonTypes.vo
linking/IprfLink.vo: specs/IprfSpec.vo sims/SimTypes.vo sims/IprfSim.vo

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
	rm -f specs/*.vo specs/*.glob specs/*.vok specs/*.vos specs/.*.aux
	rm -f sims/*.vo sims/*.glob sims/*.vok sims/*.vos sims/.*.aux
	rm -f proofs/*.vo proofs/*.glob proofs/*.vok proofs/*.vos proofs/.*.aux
	rm -f src/*.vo src/*.glob src/*.vok src/*.vos src/.*.aux
	rm -f linking/*.vo linking/*.glob linking/*.vok linking/*.vos linking/.*.aux
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

# CI targets
ci: ci-full

# Fast CI for PRs (specs + sims + proofs only)
ci-quick: clean all
	@echo "Quick CI build complete (specs + sims + proofs)!"

# Full CI for main branch (includes linking)
ci-full: clean all linking
	@echo "Full CI build complete (including linking)!"

# Audit axioms and admits (writes to artifacts for CI upload)
audit:
	@mkdir -p $(ARTIFACTS_DIR)
	@{ \
		echo "=== Plinko Axiom/Admit Audit ==="; \
		echo ""; \
		echo "Axiom declarations:"; \
		grep -rn '^Axiom' specs/ sims/ proofs/ linking/ 2>/dev/null || echo "  (none)"; \
		echo ""; \
		echo "Parameter declarations:"; \
		grep -rn '^Parameter' specs/ sims/ proofs/ linking/ 2>/dev/null || echo "  (none)"; \
		echo ""; \
		echo "Admits:"; \
		grep -rni '\badmitted\b' specs/ sims/ proofs/ linking/ 2>/dev/null || echo "  (none)"; \
	} | tee $(ARTIFACTS_DIR)/audit.txt

# Threshold for allowed admits
ADMIT_THRESHOLD ?= 10

# Check admits don't exceed threshold
check-admits:
	@echo "Checking admit count against threshold ($(ADMIT_THRESHOLD))..."
	@ADMITS=$$(grep -rni '\badmitted\b' specs/ sims/ proofs/ linking/ 2>/dev/null | wc -l | tr -d ' '); \
	if [ "$$ADMITS" -gt "$(ADMIT_THRESHOLD)" ]; then \
		echo "ERROR: admit count ($$ADMITS) exceeds threshold ($(ADMIT_THRESHOLD))"; \
		exit 1; \
	else \
		echo "OK: admit count ($$ADMITS) within threshold ($(ADMIT_THRESHOLD))"; \
	fi

# Get admit count (for CI summary)
admit-count:
	@grep -rni '\badmitted\b' specs/ sims/ proofs/ linking/ 2>/dev/null | wc -l | tr -d ' '

# Verify no unexpected axioms/parameters
AXIOM_ALLOWLIST ?= axioms_allowlist.txt
verify-axioms:
	@echo "Verifying axioms/parameters..."
	@AXIOMS=$$(grep -RnhE '^(Axiom|Parameter)' specs/ sims/ proofs/ linking/ 2>/dev/null || true); \
	if [ -z "$$AXIOMS" ]; then \
		echo "OK: no axioms/parameters found."; \
	else \
		if [ -f "$(AXIOM_ALLOWLIST)" ]; then \
			BAD=$$(echo "$$AXIOMS" | grep -v -F -f "$(AXIOM_ALLOWLIST)" || true); \
		else \
			BAD="$$AXIOMS"; \
		fi; \
		if [ -n "$$BAD" ]; then \
			echo "WARNING: non-allowlisted axioms/parameters:"; \
			echo "$$BAD"; \
		else \
			echo "OK: all axioms/parameters are allowlisted."; \
		fi; \
	fi

# Help
help:
	@echo "Plinko Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all           - Build specs, sims, and proofs (default)"
	@echo "  specs         - Build specification files"
	@echo "  sims          - Build simulation files"
	@echo "  proofs        - Build proof files"
	@echo "  translation   - Build translated Rust code (requires RocqOfRust)"
	@echo "  translate     - Re-translate Rust to Rocq (requires rocq-of-rust)"
	@echo "  linking       - Build linking layer (requires RocqOfRust)"
	@echo "  clean         - Remove all generated files"
	@echo "  check-deps    - Verify dependencies are installed"
	@echo "  ci            - Full CI build (alias for ci-full)"
	@echo "  ci-quick      - Fast CI for PRs (specs + sims + proofs)"
	@echo "  ci-full       - Full CI for main (includes linking)"
	@echo "  audit         - List axioms, parameters, and admits"
	@echo "  check-admits  - Fail if admits exceed threshold"
	@echo "  admit-count   - Print admit count (for CI summary)"
	@echo "  verify-axioms - Check for unexpected axioms/parameters"
	@echo "  help          - Show this message"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - Rocq 9.x (opam switch rocq-9)"
	@echo "  - RocqOfRust library (for 'translation' and 'linking' targets)"

-include .depend
