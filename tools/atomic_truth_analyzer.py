#!/usr/bin/env python3
"""
Analyze atomic truth steps and output their dependency structure.
Shows how complex truths are built from simple, irrefutable steps.
"""

import json

# Define atomic steps and their dependencies
atomic_steps = {
    # Peano axiom steps
    "A001.S1": {"name": "Zero exists", "deps": [], "type": "axiom"},
    "A001.S2": {"name": "Successor function exists", "deps": [], "type": "axiom"},
    "A001.S3": {"name": "Successor preserves ℕ", "deps": ["A001.S2"], "type": "deduction"},
    "A001.S4": {"name": "Zero not successor", "deps": ["A001.S1", "A001.S2"], "type": "axiom"},
    "A001.S5": {"name": "Successor injective", "deps": ["A001.S2"], "type": "axiom"},
    "A001.S6": {"name": "Induction principle", "deps": ["A001.S1", "A001.S2"], "type": "axiom"},
    
    # GF(2) field steps
    "A003.S1": {"name": "GF(2) = {0,1}", "deps": [], "type": "definition"},
    "A003.S2": {"name": "GF(2) has addition", "deps": ["A003.S1"], "type": "definition"},
    "A003.S3": {"name": "GF(2) addition table", "deps": ["A003.S1", "A003.S2"], "type": "definition"},
    "A003.S4": {"name": "GF(2) has multiplication", "deps": ["A003.S1"], "type": "definition"},
    "A003.S5": {"name": "GF(2) multiplication table", "deps": ["A003.S1", "A003.S4"], "type": "definition"},
    
    # GF(2) addition = XOR
    "T102.S1": {"name": "XOR definition", "deps": [], "type": "definition"},
    "T102.S2": {"name": "Compare tables", "deps": ["A003.S3", "T102.S1"], "type": "observation"},
    "T102.S3": {"name": "Operations equal", "deps": ["T102.S2"], "type": "deduction"},
    
    # Polynomial irreducibility
    "T200.S1": {"name": "Define p(x)", "deps": [], "type": "definition"},
    "T200.S2": {"name": "p(0) ≠ 0", "deps": ["T200.S1"], "type": "calculation"},
    "T200.S3": {"name": "p(1) ≠ 0", "deps": ["T200.S1", "A003.S3"], "type": "calculation"},
    "T200.S4": {"name": "No linear factors", "deps": ["T200.S2", "T200.S3"], "type": "deduction"},
    "T200.S5": {"name": "Computationally verified", "deps": ["T200.S1"], "type": "verification"},
    
    # XOR gate constraint
    "T300.S1": {"name": "XOR gate definition", "deps": [], "type": "definition"},
    "T300.S2": {"name": "Constraint polynomial", "deps": ["T300.S1"], "type": "definition"},
    "T300.S3": {"name": "C=0 → correct", "deps": ["T300.S2", "T102.S3"], "type": "algebra"},
    "T300.S4": {"name": "Correct → C=0", "deps": ["T300.S2", "T102.S3"], "type": "algebra"},
    "T300.S5": {"name": "Constraint complete", "deps": ["T300.S3", "T300.S4"], "type": "equivalence"},
    
    # Sumcheck soundness
    "T500.S1": {"name": "Schwartz-Zippel", "deps": [], "type": "theorem"},
    "T500.S2": {"name": "Protocol parameters", "deps": [], "type": "observation"},
    "T500.S3": {"name": "Error per round", "deps": ["T500.S1", "T500.S2"], "type": "application"},
    "T500.S4": {"name": "Union bound", "deps": ["T500.S3"], "type": "probability"},
    "T500.S5": {"name": "122-bit soundness", "deps": ["T500.S4"], "type": "conclusion"},
    
    # Zero-knowledge
    "T600.S1": {"name": "Masking setup", "deps": [], "type": "setup"},
    "T600.S2": {"name": "Vanishing polynomial", "deps": ["T600.S1"], "type": "construction"},
    "T600.S3": {"name": "Masked polynomial", "deps": ["T600.S2"], "type": "construction"},
    "T600.S4": {"name": "Evaluations preserved", "deps": ["T600.S2", "T600.S3"], "type": "calculation"},
    "T600.S5": {"name": "Perfect hiding", "deps": ["T600.S3", "T600.S4"], "type": "information"},
    
    # Combined soundness
    "T502.S1": {"name": "Error sources", "deps": [], "type": "analysis"},
    "T502.S2": {"name": "Sumcheck error", "deps": ["T500.S5"], "type": "reference"},
    "T502.S3": {"name": "Query error", "deps": [], "type": "analysis"},
    "T502.S4": {"name": "Fiat-Shamir error", "deps": [], "type": "crypto"},
    "T502.S5": {"name": "Total < 2^-121", "deps": ["T502.S2", "T502.S3", "T502.S4"], "type": "combination"}
}

# Higher-level truths that depend on atomic steps
composite_truths = {
    "A001": {"name": "Peano axioms", "deps": ["A001.S1", "A001.S2", "A001.S4", "A001.S5", "A001.S6"]},
    "A003": {"name": "GF(2) field axioms", "deps": ["A003.S1", "A003.S3", "A003.S5"]},
    "T102": {"name": "GF(2) addition = XOR", "deps": ["T102.S3"]},
    "T200": {"name": "p(x) irreducible", "deps": ["T200.S4", "T200.S5"]},
    "T300": {"name": "XOR constraint complete", "deps": ["T300.S5"]},
    "T500": {"name": "121-bit soundness", "deps": ["T500.S5"]},
    "T600": {"name": "Perfect zero-knowledge", "deps": ["T600.S5"]},
    "T502": {"name": "Combined soundness", "deps": ["T502.S5"]}
}

def find_all_deps(step_id, steps_dict):
    """Recursively find all dependencies of a step"""
    if step_id not in steps_dict:
        return set()
    
    all_deps = set()
    direct_deps = steps_dict[step_id].get('deps', [])
    
    for dep in direct_deps:
        all_deps.add(dep)
        all_deps.update(find_all_deps(dep, steps_dict))
    
    return all_deps

def print_dependency_tree(step_id, steps_dict, indent=0, visited=None):
    """Print dependency tree for a step"""
    if visited is None:
        visited = set()
    
    if step_id in visited:
        print("  " * indent + f"[{step_id}] (already shown)")
        return
    
    visited.add(step_id)
    
    if step_id in steps_dict:
        step = steps_dict[step_id]
        print("  " * indent + f"{step_id}: {step['name']} ({step.get('type', 'composite')})")
        
        for dep in step.get('deps', []):
            print_dependency_tree(dep, steps_dict, indent + 1, visited)

def main():
    print("=== ATOMIC TRUTH STEP ANALYSIS ===\n")
    
    # Combine all steps for analysis
    all_steps = {}
    all_steps.update(atomic_steps)
    all_steps.update(composite_truths)
    
    # Statistics
    print("STATISTICS:")
    print(f"  Atomic steps: {len(atomic_steps)}")
    print(f"  Composite truths: {len(composite_truths)}")
    print(f"  Total: {len(all_steps)}")
    
    # Count by type
    type_counts = {}
    for step in atomic_steps.values():
        step_type = step['type']
        type_counts[step_type] = type_counts.get(step_type, 0) + 1
    
    print("\nSTEPS BY TYPE:")
    for step_type, count in sorted(type_counts.items()):
        print(f"  {step_type}: {count}")
    
    # Find true foundations (no dependencies)
    foundations = [sid for sid, step in atomic_steps.items() if not step['deps']]
    print(f"\nTRUE FOUNDATIONS ({len(foundations)} total):")
    for sid in sorted(foundations):
        print(f"  {sid}: {atomic_steps[sid]['name']} ({atomic_steps[sid]['type']})")
    
    # Show critical path to 121-bit soundness
    print("\n=== CRITICAL PATH TO 121-BIT SOUNDNESS ===\n")
    print("Starting from T502 (Combined soundness):")
    print_dependency_tree("T502", all_steps)
    
    # Show how XOR gate constraint is built
    print("\n=== PATH TO XOR GATE CONSTRAINT ===\n")
    print("Starting from T300 (XOR constraint complete):")
    print_dependency_tree("T300", all_steps)
    
    # Show zero-knowledge construction
    print("\n=== PATH TO ZERO-KNOWLEDGE ===\n")
    print("Starting from T600 (Perfect zero-knowledge):")
    print_dependency_tree("T600", all_steps)
    
    # Analyze step complexity
    print("\n=== STEP COMPLEXITY ANALYSIS ===\n")
    
    for truth_id in ["T502", "T300", "T600"]:
        all_deps = find_all_deps(truth_id, all_steps)
        foundation_deps = [d for d in all_deps if d in foundations]
        
        print(f"{truth_id} ({composite_truths[truth_id]['name']}):")
        print(f"  Total dependencies: {len(all_deps)}")
        print(f"  Foundation dependencies: {len(foundation_deps)}")
        print(f"  Dependency depth: {max(len(find_path_to_foundation(truth_id, all_steps)))} steps")
        print()
    
    # Show the smallest atomic steps
    print("=== EXAMPLE ATOMIC STEPS ===\n")
    
    examples = ["A003.S1", "T102.S2", "T500.S3", "T600.S4"]
    for step_id in examples:
        step = atomic_steps[step_id]
        print(f"{step_id}: {step['name']}")
        print(f"  Type: {step['type']}")
        print(f"  Dependencies: {step['deps'] or 'None (foundation)'}")
        print()
    
    # Generate JSON for visualization
    output = {
        "atomic_steps": atomic_steps,
        "composite_truths": composite_truths,
        "statistics": {
            "total_atomic": len(atomic_steps),
            "total_composite": len(composite_truths),
            "foundations": len(foundations),
            "types": type_counts
        }
    }
    
    with open('atomic_truth_structure.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("Generated atomic_truth_structure.json for further analysis")

def find_path_to_foundation(step_id, steps_dict, path=None):
    """Find shortest path to a foundation (no dependencies)"""
    if path is None:
        path = []
    
    if step_id not in steps_dict:
        return path
    
    step = steps_dict[step_id]
    path = path + [step_id]
    
    if not step.get('deps'):
        return path
    
    # Find shortest path through dependencies
    shortest = None
    for dep in step['deps']:
        dep_path = find_path_to_foundation(dep, steps_dict, path)
        if shortest is None or len(dep_path) < len(shortest):
            shortest = dep_path
    
    return shortest or path

if __name__ == '__main__':
    main()