#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

import os
import re
import json
from datetime import datetime

class FStarProofGenerator:
    def __init__(self):
        self.truth_registry = {}
        self.proof_templates = {
            'axiom': self.generate_axiom_proof,
            'field': self.generate_field_proof,
            'algorithm': self.generate_algorithm_proof,
            'security': self.generate_security_proof,
            'composition': self.generate_composition_proof
        }
    
    def analyze_truth_files(self):
        """Scan truth implementation files to understand what needs proving"""
        src_dir = "modules/truth_verifier/src"
        
        for filename in os.listdir(src_dir):
            if filename.endswith("_truths.c") or filename.endswith("_axioms.c"):
                filepath = os.path.join(src_dir, filename)
                self.parse_truth_file(filepath)
    
    def parse_truth_file(self, filepath):
        """Extract truth definitions and their properties"""
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Find all verify_T### and verify_F### functions
        pattern = r'verify_([TF]\d+)_.*?\{(.*?)\n\}'
        matches = re.findall(pattern, content, re.DOTALL)
        
        for truth_id, body in matches:
            properties = self.extract_properties(truth_id, body)
            self.truth_registry[truth_id] = properties
    
    def extract_properties(self, truth_id, body):
        """Determine what kind of proof this truth needs"""
        properties = {
            'id': truth_id,
            'type': 'empirical',  # default
            'dependencies': [],
            'description': '',
            'formalization': ''
        }
        
        # Classify by content
        if 'axiom' in body.lower() or truth_id.startswith('A'):
            properties['type'] = 'axiom'
        elif 'field' in body or 'GF(2^128)' in body or 'polynomial' in body:
            properties['type'] = 'field'
        elif 'algorithm' in body or 'sumcheck' in body or 'merkle' in body:
            properties['type'] = 'algorithm'
        elif 'security' in body or 'soundness' in body or 'collision' in body:
            properties['type'] = 'security'
        elif 'composition' in body or 'recursive' in body:
            properties['type'] = 'composition'
        
        # Extract dependencies
        dep_pattern = r'depends on ([TFA]\d+)'
        dependencies = re.findall(dep_pattern, body)
        properties['dependencies'] = dependencies
        
        # Extract description
        desc_pattern = r'\/\*\s*(.*?)\s*\*\/'
        desc_match = re.search(desc_pattern, body)
        if desc_match:
            properties['description'] = desc_match.group(1).strip()
        
        return properties
    
    def generate_axiom_proof(self, truth):
        """Generate F* proof for axioms"""
        return f"""(* Axiom {truth['id']}: {truth['description']} *)

(* This is an axiom - we take it as a fundamental assumption *)
assume val axiom_{truth['id']}: unit -> Lemma
  (ensures (
    (* Axiom statement - taken as true by definition *)
    True
  ))

(* Axioms don't need proofs - they are the foundation *)
let axiom_{truth['id']} () = ()
"""

    def generate_field_proof(self, truth):
        """Generate F* proof for field arithmetic properties"""
        return f"""(* Field property {truth['id']}: {truth['description']} *)

open FStar.Mul
open GF128

(* Theorem: Field operations satisfy required properties *)
val theorem_{truth['id']}: a:gf128 -> b:gf128 -> c:gf128 -> Lemma
  (ensures (
    (* Field axioms hold *)
    (a `add` b) `add` c == a `add` (b `add` c) /\\  (* Associativity *)
    a `add` b == b `add` a /\\                       (* Commutativity *)
    a `add` zero == a /\\                            (* Identity *)
    a `add` a == zero                                (* Self-inverse *)
  ))

let theorem_{truth['id']} a b c =
  (* Field properties are proven by the GF128 module *)
  field_add_associative a b c;
  field_add_commutative a b;
  field_add_identity a;
  field_add_self_inverse a
"""

    def generate_algorithm_proof(self, truth):
        """Generate F* proof for algorithm correctness"""
        deps = ' '.join([f"open {d}_Proof" for d in truth['dependencies']])
        return f"""(* Algorithm correctness {truth['id']}: {truth['description']} *)

{deps}

(* Define the algorithm specification *)
type algorithm_spec = {{
  input: seq nat;
  output: seq nat;
  invariant: seq nat -> bool
}}

(* Theorem: Algorithm maintains invariants and produces correct output *)
val theorem_{truth['id']}: spec:algorithm_spec -> input:seq nat -> Lemma
  (requires (spec.invariant input))
  (ensures (
    let output = compute spec input in
    spec.invariant output /\\
    verify_correctness spec input output
  ))

let theorem_{truth['id']} spec input =
  (* Proof by induction on input size *)
  let rec prove_by_induction (n:nat) : Lemma
    (requires (length input == n /\\ spec.invariant input))
    (ensures (
      let output = compute spec input in
      spec.invariant output /\\ verify_correctness spec input output
    )) =
    if n = 0 then
      (* Base case: empty input *)
      base_case_proof spec
    else
      (* Inductive case *)
      let smaller = take (n-1) input in
      prove_by_induction (n-1);
      inductive_step spec smaller input
  in
  prove_by_induction (length input)
"""

    def generate_security_proof(self, truth):
        """Generate F* proof for security properties"""
        return f"""(* Security property {truth['id']}: {truth['description']} *)

open FStar.Crypto
open SecurityDefinitions

(* Define security game *)
type security_game = {{
  challenger: adversary -> challenge;
  adversary: challenge -> response;
  win_condition: challenge -> response -> bool
}}

(* Theorem: Probability of adversary winning is negligible *)
val theorem_{truth['id']}: game:security_game -> adv:adversary -> Lemma
  (ensures (
    let prob = probability_of_winning game adv in
    prob <= negligible security_parameter
  ))

let theorem_{truth['id']} game adv =
  (* Proof by reduction to cryptographic assumption *)
  let assumption = sha3_collision_resistance in
  
  (* Show that if adversary wins, we can break the assumption *)
  let reduction (win_transcript: winning_transcript game adv) : 
    sha3_collision =
    extract_collision_from_transcript win_transcript
  in
  
  (* Since SHA3 is collision resistant, winning probability is negligible *)
  assumption_implies_security assumption reduction
"""

    def generate_composition_proof(self, truth):
        """Generate F* proof for composition properties"""
        deps = ' '.join([f"open {d}_Proof" for d in truth['dependencies']])
        return f"""(* Composition property {truth['id']}: {truth['description']} *)

{deps}

(* Define composition of proofs *)
type proof_composition = {{
  proof1: proof;
  proof2: proof;
  composed: proof
}}

(* Theorem: Composition preserves soundness *)
val theorem_{truth['id']}: comp:proof_composition -> Lemma
  (requires (
    is_sound comp.proof1 /\\ is_sound comp.proof2
  ))
  (ensures (
    is_sound comp.composed /\\
    soundness_level comp.composed >= 
      min (soundness_level comp.proof1) (soundness_level comp.proof2)
  ))

let theorem_{truth['id']} comp =
  (* Proof by analyzing the composition structure *)
  let s1 = soundness_level comp.proof1 in
  let s2 = soundness_level comp.proof2 in
  
  (* Show that composed verifier accepts only if both sub-proofs verify *)
  composition_verifier_analysis comp;
  
  (* Union bound on soundness error *)
  let error_composed = error_probability comp.composed in
  let error1 = error_probability comp.proof1 in
  let error2 = error_probability comp.proof2 in
  
  assert (error_composed <= error1 + error2);
  
  (* Therefore soundness is preserved *)
  soundness_preservation_lemma comp
"""

    def generate_all_proofs(self):
        """Generate F* proofs for all unproven mathematical truths"""
        output_dir = "modules/truth_verifier/fstar/generated"
        os.makedirs(output_dir, exist_ok=True)
        
        # Check which proofs already exist
        existing_proofs = set()
        fstar_dir = "modules/truth_verifier/fstar"
        if os.path.exists(fstar_dir):
            for f in os.listdir(fstar_dir):
                if f.endswith(".fst"):
                    existing_proofs.add(f)
        
        generated_count = 0
        
        for truth_id, properties in self.truth_registry.items():
            # Skip if already has proof or is empirical
            proof_file = f"{truth_id}_Proof.fst"
            if proof_file in existing_proofs or properties['type'] == 'empirical':
                continue
            
            # Generate appropriate proof template
            proof_generator = self.proof_templates.get(
                properties['type'], 
                self.generate_algorithm_proof  # default
            )
            
            proof_content = f"""(* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 *)

module {truth_id}_Proof

(* Auto-generated F* proof template *)
(* Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} *)

{proof_generator(properties)}

(* TODO: Complete the proof details *)
"""
            
            output_path = os.path.join(output_dir, proof_file)
            with open(output_path, 'w') as f:
                f.write(proof_content)
            
            generated_count += 1
            print(f"Generated proof template: {proof_file}")
        
        return generated_count
    
    def generate_proof_makefile(self):
        """Generate Makefile for building all F* proofs"""
        makefile_content = """# F* Proof Build System
# Auto-generated - do not edit

FSTAR_HOME ?= /usr/local/share/fstar
FSTAR = $(FSTAR_HOME)/bin/fstar.exe

FSTAR_FLAGS = --cache_dir .cache --warn_error -331 \\
              --z3rlimit 50 --fuel 0 --ifuel 0

# Core modules
CORE_MODULES = \\
    MathematicalAxioms.fst \\
    GF128.fst \\
    SHA3Only.fst \\
    ZeroKnowledgeAxiom.fst

# Truth proofs
TRUTH_PROOFS = $(wildcard *_Proof.fst)

# All modules
ALL_MODULES = $(CORE_MODULES) $(TRUTH_PROOFS)

.PHONY: all verify clean

all: verify

verify: $(ALL_MODULES:.fst=.checked)

%.checked: %.fst
\t@echo "Verifying $<"
\t@$(FSTAR) $(FSTAR_FLAGS) $<
\t@touch $@

clean:
\t@rm -rf .cache *.checked

# Dependencies
T004_Proof.checked: A001_Proof.checked
T005_Proof.checked: T004_Proof.checked
T100_Proof.checked: MathematicalAxioms.checked
T101_Proof.checked: T100_Proof.checked
T102_Proof.checked: T100_Proof.checked T101_Proof.checked
T200_Proof.checked: T100_Proof.checked
T300_Proof.checked: T004_Proof.checked T200_Proof.checked
"""
        
        with open("modules/truth_verifier/fstar/Makefile", 'w') as f:
            f.write(makefile_content)
        
        print("Generated F* Makefile")
    
    def generate_summary_report(self):
        """Generate summary of proof generation"""
        report = {
            'generated_date': datetime.now().isoformat(),
            'total_truths': len(self.truth_registry),
            'by_type': {},
            'dependencies': {},
            'provable': 0,
            'empirical': 0
        }
        
        for truth_id, props in self.truth_registry.items():
            proof_type = props['type']
            report['by_type'][proof_type] = report['by_type'].get(proof_type, 0) + 1
            
            if proof_type == 'empirical':
                report['empirical'] += 1
            else:
                report['provable'] += 1
            
            if props['dependencies']:
                report['dependencies'][truth_id] = props['dependencies']
        
        with open('PROOF_GENERATION_REPORT.json', 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"\nSummary:")
        print(f"- Total truths analyzed: {report['total_truths']}")
        print(f"- Provable (mathematical): {report['provable']}")
        print(f"- Empirical only: {report['empirical']}")
        print("\nBy type:")
        for t, count in report['by_type'].items():
            print(f"  - {t}: {count}")

def main():
    print("=== F* Proof Generator for Gate Computer ===\n")
    
    generator = FStarProofGenerator()
    
    print("Analyzing truth bucket implementations...")
    generator.analyze_truth_files()
    
    print(f"\nFound {len(generator.truth_registry)} truth buckets")
    
    print("\nGenerating F* proof templates...")
    count = generator.generate_all_proofs()
    
    print(f"\nGenerated {count} new proof templates")
    
    print("\nGenerating build system...")
    generator.generate_proof_makefile()
    
    print("\nGenerating summary report...")
    generator.generate_summary_report()
    
    print("\nDone! Next steps:")
    print("1. Review generated proofs in modules/truth_verifier/fstar/generated/")
    print("2. Move completed proofs to modules/truth_verifier/fstar/")
    print("3. Run 'make verify' in the fstar directory to check proofs")

if __name__ == "__main__":
    main()