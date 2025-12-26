#!/usr/bin/env python3
"""
Translates FOPL (First-Order Predicate Logic) statements to plain English
"""

class FOPLTranslator:
    def __init__(self):
        self.predicates = {
            'Config': 'is configured',
            'EnableZK': 'has zero-knowledge enabled',
            'Witness': 'is a secret witness',
            'Random': 'is a random value',
            'Uniform': 'looks uniformly random',
            'Add': 'addition of',
            'Valid': 'is a valid pair',
            'Verifier': 'is a verifier',
            'Instance': 'is a public instance',
            'Indistinguishable': 'cannot be distinguished from',
            'View': 'what the verifier sees',
            'ZK': 'is zero-knowledge',
            'Polynomial': 'is a polynomial',
            'Field': 'is a mathematical field',
            'Degree': 'has degree',
            'Rounds': 'uses rounds',
            'GatePolynomial': 'is a gate polynomial',
            'CircuitSize': 'has circuit size',
            'SecurityBits': 'has security level in bits',
            'HashOperation': 'is a hashing operation',
            'InSystem': 'is in our system',
            'UseSHA3': 'uses SHA3',
            'ConstantTime': 'runs in constant time',
            'TimingLeak': 'has timing leaks',
            'Entropy': 'has entropy source',
            'Verified': 'is verified',
            'Implementation': 'is the implementation',
            'Specification': 'matches the specification'
        }
        
        self.quantifiers = {
            '∀': 'for every',
            '∃': 'there exists',
            '∄': 'there does not exist'
        }
        
        self.connectives = {
            '→': 'implies',
            '↔': 'if and only if',
            '∧': 'and',
            '∨': 'or',
            '¬': 'not',
            '⊥': 'contradiction',
            '⊤': 'tautology (always true)'
        }
        
    def translate_formula(self, formula, context=""):
        """Translate a FOPL formula to English"""
        # This is a simplified translator for demonstration
        examples = {
            "∀x(Config(x) → EnableZK(x))": 
                "For every system x: if x is configured, then x has zero-knowledge enabled",
            
            "∀w∀r(Witness(w) ∧ Random(r) → Uniform(Add(w,r)))":
                "For every witness w and random value r: if w is a secret witness and r is random, then adding them together looks uniformly random",
            
            "∀h∀op(HashOperation(op) ∧ InSystem(op) → UseSHA3(op))":
                "For every hash function h and operation op: if op is a hashing operation in our system, then op must use SHA3",
            
            "∃s∀v(Verifier(v) → ¬Distinguishable(RealProof, s()))":
                "There exists a simulator s such that for every verifier v: the verifier cannot distinguish the real proof from the simulator's output",
            
            "∀t(TimingLeak(t) → ¬ConstantTime(t))":
                "For every timing leak t: if t is a timing leak, then t does not run in constant time",
            
            "∀e(Entropy(e) → ∃v(Verified(e,v) ∧ v ≥ 128))":
                "For every entropy source e: if e is an entropy source, then there exists a verification v such that e is verified with at least 128 bits",
            
            "P(CheatingSucceeds) ≤ 2^(-122)":
                "The probability of successfully cheating is at most 1 in 2^122 (about 1 in 5 septillion)",
            
            "∀i∀s(Implementation(i) ∧ Specification(s) → Matches(i,s))":
                "For every implementation i and specification s: the implementation must match the specification"
        }
        
        return examples.get(formula, f"[Translation pending for: {formula}]")
    
    def translate_proof_line(self, line):
        """Translate a single line of a FOPL proof"""
        # Extract components
        if " → " in line:
            parts = line.split(" → ")
            premise = self.translate_formula(parts[0])
            conclusion = self.translate_formula(parts[1])
            return f"If {premise}, then {conclusion}"
        
        return self.translate_formula(line)
    
    def explain_inference_rule(self, rule):
        """Explain common inference rules in plain English"""
        rules = {
            "Modus Ponens": 
                "If we know 'A implies B' and we know 'A is true', then we can conclude 'B is true'",
            
            "Universal Instantiation":
                "If something is true for ALL things, then it's true for this SPECIFIC thing",
            
            "Existential Generalization":
                "If we found ONE example that works, we can say 'there exists something that works'",
            
            "Conjunction":
                "If A is true AND B is true, then 'A and B' is true",
            
            "Schwartz-Zippel Lemma":
                "A non-zero polynomial of degree d over a field F has at most d roots, so randomly hitting a root has probability at most d/|F|",
            
            "Axiom":
                "A fundamental truth we accept without proof (like 'zero-knowledge is mandatory')",
            
            "Definition":
                "This is what we mean when we use this term",
            
            "Arithmetic":
                "Basic mathematical calculation",
            
            "From Implementation":
                "This follows from how the code actually works"
        }
        
        return rules.get(rule, f"[Inference rule: {rule}]")

def demonstrate_translations():
    translator = FOPLTranslator()
    
    print("FOPL TO ENGLISH TRANSLATIONS")
    print("=" * 80)
    
    # Core axioms
    print("\n## CORE AXIOMS\n")
    
    axioms = [
        ("A001", "∀h∀op(HashOperation(op) ∧ InSystem(op) → UseSHA3(op))", 
         "SHA3-only constraint"),
        ("A002", "∀x(Config(x) → EnableZK(x))", 
         "Zero-knowledge is mandatory"),
        ("Field", "|GF(2^128)| = 2^128",
         "The field GF(2^128) has exactly 2^128 elements (about 340 undecillion)")
    ]
    
    for axiom_id, formula, description in axioms:
        print(f"**{axiom_id}**: {description}")
        print(f"FOPL: `{formula}`")
        print(f"English: {translator.translate_formula(formula)}")
        print()
    
    # Security properties
    print("\n## SECURITY PROPERTIES\n")
    
    security_props = [
        ("Soundness", "∀π∀x(¬Valid(x) → P(Verify(π,x)) ≤ 2^(-122))",
         "Invalid statements have negligible chance of false proofs"),
        ("Zero-Knowledge", "∃s∀v∀x∀w(Valid(x,w) → Indistinguishable(View(v,π,x,w), s(x)))",
         "Valid proofs reveal nothing beyond validity"),
        ("Completeness", "∀x∀w(Valid(x,w) → ∃π(Verify(π,x) = true))",
         "All valid statements have proofs")
    ]
    
    for prop_name, formula, plain_english in security_props:
        print(f"**{prop_name}**")
        print(f"FOPL: `{formula}`")
        print(f"Plain English: {plain_english}")
        print()
    
    # Common patterns
    print("\n## COMMON PROOF PATTERNS\n")
    
    patterns = [
        ("Confidence Boost", 
         "∀t∀w(Truth(t) ∧ WIPTruth(w) ∧ Addresses(w,t) ∧ Verified(w) → Confidence(t) += Boost(w))",
         "When we verify a supporting WIP truth that addresses a concern, it boosts confidence in the main truth"),
        
        ("Security Preservation",
         "∀opt∀sec(Optimization(opt) ∧ SecurityProperty(sec) ∧ HoldsBefore(sec) → HoldsAfter(sec, opt))",
         "Every optimization must preserve all security properties"),
        
        ("Performance Reality Check",
         "∀claim∀measurement(PerformanceClaim(claim) ∧ Measured(measurement) → claim ≈ measurement)",
         "Performance claims must match actual measurements")
    ]
    
    for pattern_name, formula, explanation in patterns:
        print(f"**{pattern_name}**")
        print(f"Pattern: `{formula}`")
        print(f"Meaning: {explanation}")
        print()
    
    # Inference rules
    print("\n## INFERENCE RULES EXPLAINED\n")
    
    for rule in ["Modus Ponens", "Universal Instantiation", "Schwartz-Zippel Lemma", "Axiom"]:
        print(f"**{rule}**: {translator.explain_inference_rule(rule)}")
        print()

if __name__ == "__main__":
    demonstrate_translations()
    
    print("\n## EXAMPLE: PROVING 99% CONFIDENCE\n")
    print("To prove a truth reaches 99% confidence after WIP truths:")
    print()
    print("FOPL: ∀t∈Truths(Confidence(t) ≥ 0.99 ↔ ∀w∈WIP(t)(Verified(w)))")
    print()
    print("English: For every truth t in our system, t achieves 99% confidence")
    print("if and only if all of its supporting WIP truths have been verified.")
    print()
    print("This is why we generate WIP truths - they're the logical building blocks")
    print("that, when verified, mathematically guarantee 99% confidence!")