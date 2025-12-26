#!/usr/bin/env python3
"""
Generate a dependency graph showing atomic truth steps and their relationships.
Each step is so small and simple that it cannot be disputed.
"""

import json
import graphviz

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
    "A001": {"name": "Peano axioms", "deps": ["A001.S1", "A001.S2", "A001.S4", "A001.S5", "A001.S6"], "type": "axiom_set"},
    "A003": {"name": "GF(2) field axioms", "deps": ["A003.S1", "A003.S3", "A003.S5"], "type": "axiom_set"},
    "T102": {"name": "GF(2) addition = XOR", "deps": ["T102.S3"], "type": "truth"},
    "T200": {"name": "p(x) irreducible", "deps": ["T200.S4", "T200.S5"], "type": "truth"},
    "T300": {"name": "XOR constraint complete", "deps": ["T300.S5"], "type": "truth"},
    "T500": {"name": "121-bit soundness", "deps": ["T500.S5"], "type": "truth"},
    "T600": {"name": "Perfect zero-knowledge", "deps": ["T600.S5"], "type": "truth"},
    "T502": {"name": "Combined soundness", "deps": ["T502.S5"], "type": "truth"}
}

def create_atomic_graph():
    """Create a graph showing atomic truth dependencies"""
    dot = graphviz.Digraph(comment='Atomic Truth Steps', engine='dot')
    dot.attr(rankdir='BT', nodesep='0.5', ranksep='1.0')
    
    # Define colors for different types
    colors = {
        'axiom': '#ff6b6b',
        'definition': '#4ecdc4',
        'deduction': '#45b7d1',
        'calculation': '#96ceb4',
        'observation': '#feca57',
        'theorem': '#ff9ff3',
        'algebra': '#54a0ff',
        'equivalence': '#10ac84',
        'probability': '#ee5a6f',
        'verification': '#ff4757',
        'application': '#48dbfb',
        'construction': '#f368e0',
        'information': '#00d2d3',
        'setup': '#c8d6e5',
        'analysis': '#576574',
        'reference': '#01a3a4',
        'crypto': '#ee5a24',
        'combination': '#341f97',
        'axiom_set': '#ff6b6b',
        'truth': '#2e86ab'
    }
    
    # Create subgraphs for different categories
    with dot.subgraph(name='cluster_peano') as c:
        c.attr(label='Peano Axioms', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('A001'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'),
                      shape='box' if step['type'] == 'axiom' else 'ellipse')
    
    with dot.subgraph(name='cluster_gf2') as c:
        c.attr(label='GF(2) Field', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('A003'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'),
                      shape='box' if step['type'] in ['axiom', 'definition'] else 'ellipse')
    
    with dot.subgraph(name='cluster_xor_equals') as c:
        c.attr(label='GF(2) = XOR', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('T102'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    with dot.subgraph(name='cluster_irreducible') as c:
        c.attr(label='Polynomial Irreducibility', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('T200'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    with dot.subgraph(name='cluster_constraint') as c:
        c.attr(label='XOR Gate Constraint', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('T300'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    with dot.subgraph(name='cluster_sumcheck') as c:
        c.attr(label='Sumcheck Soundness', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('T500'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    with dot.subgraph(name='cluster_zk') as c:
        c.attr(label='Zero-Knowledge', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('T600'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    with dot.subgraph(name='cluster_combined') as c:
        c.attr(label='Combined Soundness', style='filled', color='lightgrey')
        for step_id, step in atomic_steps.items():
            if step_id.startswith('T502'):
                c.node(step_id, f"{step_id}\n{step['name']}", 
                      style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    # Add remaining nodes
    for step_id, step in atomic_steps.items():
        if not any(step_id.startswith(prefix) for prefix in ['A001', 'A003', 'T102', 'T200', 'T300', 'T500', 'T600', 'T502']):
            dot.node(step_id, f"{step_id}\n{step['name']}", 
                    style='filled', fillcolor=colors.get(step['type'], 'white'))
    
    # Add composite truth nodes
    with dot.subgraph(name='cluster_composite') as c:
        c.attr(label='Composite Truths', style='filled', color='lightblue')
        for truth_id, truth in composite_truths.items():
            c.node(truth_id, f"{truth_id}\n{truth['name']}", 
                  style='filled,bold', fillcolor=colors.get(truth['type'], 'white'),
                  shape='doubleoctagon')
    
    # Add edges for atomic steps
    for step_id, step in atomic_steps.items():
        for dep in step['deps']:
            dot.edge(dep, step_id)
    
    # Add edges for composite truths
    for truth_id, truth in composite_truths.items():
        for dep in truth['deps']:
            dot.edge(dep, truth_id, style='dashed', color='blue')
    
    # Add legend
    with dot.subgraph(name='cluster_legend') as c:
        c.attr(label='Step Types', style='filled', color='white')
        c.attr(rank='same')
        for step_type, color in sorted(colors.items()):
            c.node(f'legend_{step_type}', step_type, 
                  style='filled', fillcolor=color, shape='box')
    
    return dot

def create_critical_path_graph():
    """Create a graph showing only the critical path to key results"""
    dot = graphviz.Digraph(comment='Critical Path', engine='dot')
    dot.attr(rankdir='BT', nodesep='0.5', ranksep='1.5')
    
    # Critical path to 121-bit soundness
    critical_path = {
        # GF(2) = XOR path
        "A003.S1": "GF(2) = {0,1}",
        "A003.S3": "Addition table",
        "T102.S1": "XOR definition",
        "T102.S2": "Tables match",
        "T102.S3": "GF(2) + = XOR",
        
        # Soundness path
        "T500.S1": "Schwartz-Zippel",
        "T500.S2": "d=3, |F|=2^128",
        "T500.S3": "3/2^128 per round",
        "T500.S4": "17 rounds total",
        "T500.S5": "Error < 2^-122",
        
        # Combined path
        "T502.S2": "Sumcheck: 2^-122",
        "T502.S3": "Queries: 2^-133",
        "T502.S5": "Total < 2^-121",
        
        # Final result
        "T502": "121-bit security"
    }
    
    # Add nodes
    for node_id, label in critical_path.items():
        if node_id.startswith('A'):
            color = '#ff6b6b'
        elif node_id.startswith('T1'):
            color = '#4ecdc4'
        elif node_id.startswith('T5'):
            color = '#ff9ff3'
        else:
            color = '#2e86ab'
        
        dot.node(node_id, f"{node_id}\n{label}", 
                style='filled', fillcolor=color,
                shape='doubleoctagon' if '.' not in node_id else 'box')
    
    # Add edges showing the critical path
    edges = [
        ("A003.S1", "A003.S3"),
        ("A003.S3", "T102.S2"),
        ("T102.S1", "T102.S2"),
        ("T102.S2", "T102.S3"),
        ("T500.S1", "T500.S3"),
        ("T500.S2", "T500.S3"),
        ("T500.S3", "T500.S4"),
        ("T500.S4", "T500.S5"),
        ("T500.S5", "T502.S2"),
        ("T502.S2", "T502.S5"),
        ("T502.S3", "T502.S5"),
        ("T502.S5", "T502")
    ]
    
    for src, dst in edges:
        dot.edge(src, dst, penwidth='2')
    
    return dot

def main():
    # Generate the full atomic dependency graph
    print("Generating atomic truth dependency graph...")
    graph = create_atomic_graph()
    graph.render('atomic_truth_dependencies', format='png', cleanup=True)
    graph.render('atomic_truth_dependencies', format='pdf', cleanup=True)
    
    # Generate the critical path graph
    print("Generating critical path graph...")
    critical = create_critical_path_graph()
    critical.render('critical_path_to_soundness', format='png', cleanup=True)
    critical.render('critical_path_to_soundness', format='pdf', cleanup=True)
    
    # Generate statistics
    print("\nAtomic Truth Statistics:")
    print(f"Total atomic steps: {len(atomic_steps)}")
    print(f"Composite truths: {len(composite_truths)}")
    
    # Count by type
    type_counts = {}
    for step in atomic_steps.values():
        step_type = step['type']
        type_counts[step_type] = type_counts.get(step_type, 0) + 1
    
    print("\nSteps by type:")
    for step_type, count in sorted(type_counts.items()):
        print(f"  {step_type}: {count}")
    
    # Find steps with no dependencies (true axioms/definitions)
    no_deps = [sid for sid, step in atomic_steps.items() if not step['deps']]
    print(f"\nTrue foundations (no dependencies): {len(no_deps)}")
    for sid in sorted(no_deps):
        print(f"  {sid}: {atomic_steps[sid]['name']}")
    
    print("\nGraphs generated:")
    print("  - atomic_truth_dependencies.png/pdf")
    print("  - critical_path_to_soundness.png/pdf")

if __name__ == '__main__':
    main()