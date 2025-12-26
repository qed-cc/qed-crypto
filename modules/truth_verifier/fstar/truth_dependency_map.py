#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

"""
Truth Dependency Map for Gate Computer
Visualizes how truths trace back to fundamental axioms
"""

import json

# Define the truth hierarchy
truth_hierarchy = {
    "axioms": {
        "A001": {
            "statement": "Only SHA3 is allowed for hashing",
            "confidence": 100,
            "category": "axiom",
            "children": ["T064", "T202", "T400", "T600"]
        },
        "A002": {
            "statement": "All proofs MUST be zero-knowledge",
            "confidence": 100,
            "category": "axiom", 
            "children": ["T-ZK001", "T203", "T801"]
        },
        "A003": {
            "statement": "GF(2) field axioms",
            "confidence": 100,
            "category": "mathematical",
            "children": ["T100", "T101"]
        },
        "A004": {
            "statement": "Boolean algebra axioms",
            "confidence": 100,
            "category": "mathematical",
            "children": ["T104", "T202"]
        },
        "A005": {
            "statement": "Logic axioms",
            "confidence": 100,
            "category": "mathematical",
            "children": ["T204"]
        }
    },
    "truths": {
        # Security truths
        "T004": {
            "statement": "Effective soundness is 122 bits (not 128)",
            "confidence": 99.5,
            "category": "security",
            "parents": ["T504"],
            "children": ["T206", "T804"]
        },
        "T005": {
            "statement": "Post-quantum secure (no discrete log)",
            "confidence": 99.2,
            "category": "security",
            "parents": ["T201", "T802"],
            "children": []
        },
        
        # SHA3 constraint truths
        "T064": {
            "statement": "SHA3-256 requires 200K gates",
            "confidence": 99.7,
            "category": "implementation",
            "parents": ["A001"],
            "children": ["T066", "T600"]
        },
        "T202": {
            "statement": "Uses SHA3-256 for collision resistance", 
            "confidence": 99.8,
            "category": "security",
            "parents": ["A001"],
            "children": ["T301", "T603"]
        },
        
        # ZK truths
        "T203": {
            "statement": "Polynomial masking provides zero-knowledge",
            "confidence": 99.8,
            "category": "security",
            "parents": ["A002"],
            "children": ["T801"]
        },
        "T-ZK001": {
            "statement": "Zero-knowledge overhead is negligible (<1%)",
            "confidence": 99.9,
            "category": "zk",
            "parents": ["A002"],
            "children": []
        },
        
        # Mathematical foundation
        "T100": {
            "statement": "Binary field properties (XOR = addition)",
            "confidence": 99.9,
            "category": "math",
            "parents": ["A003"],
            "children": ["T200"]
        },
        "T200": {
            "statement": "XOR gate properties fully constrained",
            "confidence": 99.8,
            "category": "gates",
            "parents": ["T100"],
            "children": ["T400", "T500"]
        },
        "T201": {
            "statement": "AND gate completeness in GF(2^128)",
            "confidence": 99.8,
            "category": "gates",
            "parents": ["T103"],
            "children": ["T401", "T500"]
        },
        
        # SHA3 circuit truths
        "T400": {
            "statement": "SHA3 XOR gates fully constrained",
            "confidence": 99.6,
            "category": "circuits",
            "parents": ["T200", "A001"],
            "children": ["T404", "T500"]
        },
        "T401": {
            "statement": "SHA3 AND gates fully constrained",
            "confidence": 99.6,
            "category": "circuits",
            "parents": ["T201", "T302"],
            "children": ["T404", "T500"]
        },
        
        # Constraint system
        "T500": {
            "statement": "Unique witness property",
            "confidence": 99.5,
            "category": "constraints",
            "parents": ["T200", "T201", "T404"],
            "children": ["T501", "T502"]
        },
        "T504": {
            "statement": "Soundness error bound 2^(-121)",
            "confidence": 99.5,
            "category": "security",
            "parents": ["T503"],
            "children": ["T004", "T800"]
        },
        
        # System level
        "T800": {
            "statement": "BaseFold RAA soundness",
            "confidence": 99.2,
            "category": "system",
            "parents": ["T504", "T602"],
            "children": ["T804"]
        },
        "T801": {
            "statement": "Perfect zero-knowledge",
            "confidence": 99.2,
            "category": "system",
            "parents": ["T203", "A002"],
            "children": ["T804"]
        },
        "T804": {
            "statement": "121-bit security achieved",
            "confidence": 99.2,
            "category": "system",
            "parents": ["T800", "T801", "T802", "T803"],
            "children": ["MASTER_CIRCUITS"]
        },
        
        # Master truth
        "MASTER_CIRCUITS": {
            "statement": "All circuits fully constrained and secure",
            "confidence": 99.0,
            "category": "master",
            "parents": ["T804"],
            "children": []
        }
    }
}

def print_dependency_tree(node_id, nodes, level=0, visited=None):
    """Print truth dependencies as a tree"""
    if visited is None:
        visited = set()
    
    if node_id in visited:
        print("  " * level + f"[{node_id}] (circular reference)")
        return
    
    visited.add(node_id)
    
    # Find node in axioms or truths
    node = None
    if node_id in truth_hierarchy["axioms"]:
        node = truth_hierarchy["axioms"][node_id]
    elif node_id in truth_hierarchy["truths"]:
        node = truth_hierarchy["truths"][node_id]
    
    if not node:
        print("  " * level + f"[{node_id}] (not found)")
        return
    
    # Print node info
    confidence = node.get("confidence", "?")
    statement = node["statement"]
    print("  " * level + f"[{node_id}] {statement} ({confidence}%)")
    
    # Print children
    for child in node.get("children", []):
        print_dependency_tree(child, nodes, level + 1, visited.copy())

def trace_to_axioms(truth_id, visited=None):
    """Trace a truth back to its axioms"""
    if visited is None:
        visited = set()
    
    if truth_id in visited:
        return []
    
    visited.add(truth_id)
    
    # Check if this is an axiom
    if truth_id in truth_hierarchy["axioms"]:
        return [truth_id]
    
    # Find the truth
    if truth_id not in truth_hierarchy["truths"]:
        return []
    
    truth = truth_hierarchy["truths"][truth_id]
    axioms = []
    
    # Trace through parents
    for parent in truth.get("parents", []):
        parent_axioms = trace_to_axioms(parent, visited.copy())
        axioms.extend(parent_axioms)
    
    return list(set(axioms))  # Remove duplicates

def main():
    print("=== GATE COMPUTER TRUTH DEPENDENCY MAP ===\n")
    
    # Show key axioms
    print("FUNDAMENTAL AXIOMS:")
    for axiom_id, axiom in truth_hierarchy["axioms"].items():
        print(f"  {axiom_id}: {axiom['statement']}")
    
    print("\n" + "="*50 + "\n")
    
    # Show how key truths trace to axioms
    key_truths = ["T004", "T005", "T201", "T203", "T504", "T801", "T804", "MASTER_CIRCUITS"]
    
    print("KEY TRUTH DEPENDENCIES:\n")
    for truth_id in key_truths:
        if truth_id in truth_hierarchy["truths"]:
            truth = truth_hierarchy["truths"][truth_id]
            axioms = trace_to_axioms(truth_id)
            print(f"{truth_id}: {truth['statement']}")
            print(f"  Confidence: {truth['confidence']}%")
            print(f"  Traces to axioms: {', '.join(axioms)}")
            print()
    
    print("\n" + "="*50 + "\n")
    
    # Show dependency trees from axioms
    print("DEPENDENCY TREES FROM AXIOMS:\n")
    for axiom_id in ["A001", "A002"]:
        print(f"From {axiom_id}:")
        print_dependency_tree(axiom_id, truth_hierarchy)
        print()
    
    # Export to JSON for visualization tools
    with open("truth_dependencies.json", "w") as f:
        json.dump(truth_hierarchy, f, indent=2)
    print("\nExported to truth_dependencies.json for visualization")

if __name__ == "__main__":
    main()