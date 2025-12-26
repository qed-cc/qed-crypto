#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

"""
Generate a visual graph showing proof dependencies between truths
"""

import json
import graphviz
import re

# Define proof dependencies
proof_dependencies = {
    # Security foundation
    "T-SEC001": ["T-SEC002", "T-SEC003", "T-SEC006"],  # 121-bit depends on components
    "T-SEC002": ["AXIOM-GF128"],  # Sumcheck depends on field
    "T-SEC003": ["AXIOM-SHA3"],   # SHA3 security is axiomatic
    "T-SEC004": ["T-SEC001"],      # Quantum depends on classical
    "T-SEC005": ["AXIOM-ZK"],      # ZK is required axiom
    "T-SEC006": ["T-SEC002", "T-SEC003"],  # No vulnerability proven by components
    "T-SEC007": ["T-SEC001", "T-SEC005"],  # Recursive preserves both
    "T-SEC008": ["T-SEC001"],      # Implementation matches theory
    
    # Performance proofs
    "T-R001": ["T-SEC002"],        # Algebraic aggregation preserves sumcheck
    "T-R002": ["T-SEC003"],        # Circuit reduction still uses SHA3
    "T-R003": ["T-R001"],          # Batch verification uses aggregation
    "T-R004": ["T-SEC002"],        # Streaming preserves sumcheck
    "T-R005": ["T-SEC003"],        # Parallel Merkle uses deterministic SHA3
    "T-R006": ["T-R003", "T-R005"], # Optimal batch from both
    "T-R007": ["EMPIRICAL"],       # Memory bandwidth empirical
    "T-R008": ["T-R001", "T-R002", "T-R003", "T-R004", "T-R005", "T-R006"],
    
    # Correctness proofs
    "T702A": ["T-SEC007", "T-R008"],  # Circular needs recursive security + performance
    "T707": ["T-SEC001", "T-SEC005"], # Complete system needs security + ZK
    
    # Axioms (no dependencies)
    "AXIOM-SHA3": [],
    "AXIOM-ZK": [],
    "AXIOM-GF128": [],
    "EMPIRICAL": []
}

# Proof types for coloring
proof_types = {
    "AXIOM-SHA3": "axiom",
    "AXIOM-ZK": "axiom", 
    "AXIOM-GF128": "axiom",
    "EMPIRICAL": "empirical",
    "T-SEC001": "security",
    "T-SEC002": "security",
    "T-SEC003": "security",
    "T-SEC004": "security",
    "T-SEC005": "security",
    "T-SEC006": "security",
    "T-SEC007": "security",
    "T-SEC008": "security",
    "T-R001": "performance",
    "T-R002": "performance",
    "T-R003": "performance",
    "T-R004": "performance",
    "T-R005": "performance",
    "T-R006": "performance",
    "T-R007": "performance",
    "T-R008": "performance",
    "T702A": "correctness",
    "T707": "correctness"
}

# Color scheme
colors = {
    "axiom": "#FFD700",       # Gold
    "security": "#FF6B6B",    # Red
    "performance": "#4ECDC4", # Teal
    "correctness": "#95E1D3", # Light green
    "empirical": "#C7CEEA"    # Lavender
}

def generate_proof_graph():
    """Generate a directed graph of proof dependencies"""
    
    dot = graphviz.Digraph(comment='Truth Bucket Proof Dependencies')
    dot.attr(rankdir='BT')  # Bottom to top
    dot.attr(size='12,10')
    dot.attr(dpi='150')
    
    # Add title
    dot.attr(label='Gate Computer Truth Bucket Proof Dependencies', fontsize='20')
    
    # Add all nodes
    for truth_id in proof_dependencies:
        proof_type = proof_types.get(truth_id, "unknown")
        color = colors.get(proof_type, "#FFFFFF")
        
        # Special shapes for different types
        if proof_type == "axiom":
            shape = "box"
            style = "filled,bold"
        elif proof_type == "empirical":
            shape = "ellipse"
            style = "filled,dashed"
        else:
            shape = "ellipse"
            style = "filled"
            
        dot.node(truth_id, truth_id, fillcolor=color, style=style, shape=shape)
    
    # Add edges (dependencies)
    for truth_id, deps in proof_dependencies.items():
        for dep in deps:
            dot.edge(dep, truth_id)
    
    # Add legend
    with dot.subgraph(name='cluster_legend') as legend:
        legend.attr(label='Legend', style='filled', color='lightgray')
        legend.node('L1', 'Axiom', shape='box', fillcolor=colors['axiom'], style='filled,bold')
        legend.node('L2', 'Security', fillcolor=colors['security'], style='filled')
        legend.node('L3', 'Performance', fillcolor=colors['performance'], style='filled')
        legend.node('L4', 'Correctness', fillcolor=colors['correctness'], style='filled')
        legend.node('L5', 'Empirical', fillcolor=colors['empirical'], style='filled,dashed')
        
        # Invisible edges to layout legend vertically
        legend.edge('L1', 'L2', style='invis')
        legend.edge('L2', 'L3', style='invis')
        legend.edge('L3', 'L4', style='invis')
        legend.edge('L4', 'L5', style='invis')
    
    # Save the graph
    dot.render('proof_dependencies', format='png', cleanup=True)
    dot.render('proof_dependencies', format='pdf', cleanup=True)
    print("Generated proof_dependencies.png and proof_dependencies.pdf")
    
    # Also generate a text summary
    print("\nProof Dependency Summary:")
    print("========================")
    
    # Find root truths (no incoming edges)
    all_deps = set()
    for deps in proof_dependencies.values():
        all_deps.update(deps)
    
    roots = set(proof_dependencies.keys()) - all_deps
    print(f"\nRoot Truths (proven from axioms): {sorted(roots)}")
    
    # Find leaf truths (no outgoing edges)
    leaves = [t for t, deps in proof_dependencies.items() if not deps]
    print(f"\nAxiomatic/Empirical Truths: {sorted(leaves)}")
    
    # Calculate proof depth
    def get_depth(truth_id, memo={}):
        if truth_id in memo:
            return memo[truth_id]
        
        deps = proof_dependencies.get(truth_id, [])
        if not deps:
            depth = 0
        else:
            depth = 1 + max(get_depth(d, memo) for d in deps)
        
        memo[truth_id] = depth
        return depth
    
    print("\nProof Depths:")
    depths = [(t, get_depth(t)) for t in proof_dependencies]
    for truth_id, depth in sorted(depths, key=lambda x: (-x[1], x[0])):
        print(f"  {truth_id}: depth {depth}")

if __name__ == "__main__":
    generate_proof_graph()