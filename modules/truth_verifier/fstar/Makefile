# Makefile for F* proof verification
# This currently documents what proofs exist, since F* isn't built

.PHONY: all list verify extract demo help

FSTAR_FILES := $(wildcard *.fst)
PROOF_COUNT := $(words $(FSTAR_FILES))

help:
	@echo "F* Proof System ($(PROOF_COUNT) proof files)"
	@echo "======================================"
	@echo "F* provides compile-time mathematical proofs of our truth buckets."
	@echo ""
	@echo "Available commands:"
	@echo "  make list     - List all proof files"
	@echo "  make verify   - Verify all proofs (requires F* installation)"
	@echo "  make extract  - Extract C code from proofs (requires F*)"
	@echo "  make demo     - Show example proofs"
	@echo ""
	@echo "To use F*, install:"
	@echo "  1. OCaml >= 4.08"
	@echo "  2. OPAM"
	@echo "  3. F* dependencies via: opam install batteries zarith stdint yojson"
	@echo ""
	@echo "Current status: F* specifications exist but compiler not installed"

list:
	@echo "=== F* Proof Files ($(PROOF_COUNT) total) ==="
	@for f in $(FSTAR_FILES); do \
		echo "  $$f"; \
	done
	@echo ""
	@echo "Key proofs:"
	@echo "  - BaseFoldSecurity.fst: 121-bit soundness proof"
	@echo "  - SHA3Only.fst: SHA3-only axiom verification"
	@echo "  - CompileTimeProofs.fst: Compile-time truth verification"
	@echo "  - TruthBucket.fst: Truth bucket system formalization"

demo:
	@echo "=== Example F* Proofs ==="
	@echo ""
	@echo "1. Compile-time proof that soundness is 121 bits:"
	@grep -A3 "val soundness_is_121_bits" CompileTimeProofs.fst || true
	@echo ""
	@echo "2. SHA3-only axiom:"
	@grep -A3 "val only_sha3_allowed" SHA3Only.fst || true
	@echo ""
	@echo "3. Zero-knowledge requirement:"
	@grep -A3 "val zk_is_mandatory" BaseFoldSecurity.fst || true

verify:
	@echo "ERROR: F* not installed. To verify proofs:"
	@echo "  1. Install OCaml and OPAM"
	@echo "  2. Build F* in vendor/FStar"
	@echo "  3. Run: make verify"

extract:
	@echo "ERROR: F* not installed. Cannot extract C code from proofs."

all: help