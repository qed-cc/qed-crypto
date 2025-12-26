#!/usr/bin/env python3
"""Generate a graphical visualization of the truth dependency tree"""

import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import FancyBboxPatch, ConnectionPatch
import numpy as np

# Set up the figure
fig, ax = plt.subplots(1, 1, figsize=(16, 20))
ax.set_xlim(0, 100)
ax.set_ylim(0, 140)
ax.axis('off')

# Color scheme
colors = {
    'axiom': '#FF6B6B',      # Red
    'crypto': '#FFE66D',     # Yellow
    'gate': '#4ECDC4',       # Teal
    'security': '#45B7D1',   # Blue
    'protocol': '#DDA0DD',   # Plum
    'performance': '#98D8C8', # Mint
    'master': '#90EE90'      # Light green
}

# Node positions
nodes = {
    # Level 0: Mathematical Axioms
    'logic': (10, 10),
    'set_theory': (30, 10),
    'peano': (50, 10),
    'field': (70, 10),
    
    # Level 1: Crypto
    'info_theory': (20, 25),
    'sha3_foundation': (60, 25),
    
    # Level 2: Gate Computer Axioms
    'A001': (25, 40),
    'A002': (55, 40),
    
    # Level 3: Security Properties
    'T201': (15, 55),
    'T202': (35, 55),
    'T203': (55, 55),
    'T005': (75, 55),
    
    # Level 4: Protocol Properties
    'T004': (25, 70),
    'T303': (50, 70),
    'T801': (75, 70),
    
    # Level 5: Performance
    'T150': (50, 85),
    
    # Master
    'MASTER': (50, 100)
}

# Draw nodes
def draw_node(name, pos, text, color, width=15, height=5):
    x, y = pos
    box = FancyBboxPatch(
        (x - width/2, y - height/2), width, height,
        boxstyle="round,pad=0.3",
        facecolor=color,
        edgecolor='black',
        linewidth=2
    )
    ax.add_patch(box)
    
    # Add text
    ax.text(x, y, text, ha='center', va='center', 
            fontsize=9, fontweight='bold', wrap=True)

# Draw connections
def draw_arrow(start, end, style='solid', color='black'):
    x1, y1 = nodes[start]
    x2, y2 = nodes[end]
    
    arrow = ConnectionPatch(
        (x1, y1 + 2.5), (x2, y2 - 2.5),
        "data", "data",
        arrowstyle="->",
        shrinkA=0, shrinkB=0,
        mutation_scale=20,
        fc=color,
        linestyle=style,
        linewidth=2
    )
    ax.add_artist(arrow)

# Draw all nodes
# Level 0
draw_node('logic', nodes['logic'], 'LOGIC\nAXIOMS', colors['axiom'], 12, 6)
draw_node('set_theory', nodes['set_theory'], 'SET\nTHEORY', colors['axiom'], 12, 6)
draw_node('peano', nodes['peano'], 'PEANO\nAXIOMS', colors['axiom'], 12, 6)
draw_node('field', nodes['field'], 'FIELD\nAXIOMS', colors['axiom'], 12, 6)

# Level 1
draw_node('info_theory', nodes['info_theory'], 'INFORMATION\nTHEORY', colors['crypto'], 14, 6)
draw_node('sha3_foundation', nodes['sha3_foundation'], 'SHA3/KECCAK\nFOUNDATION', colors['crypto'], 14, 6)

# Level 2
draw_node('A001', nodes['A001'], 'A001:\nSHA3-ONLY', colors['gate'], 14, 6)
draw_node('A002', nodes['A002'], 'A002:\nZK-ALWAYS', colors['gate'], 14, 6)

# Level 3
draw_node('T201', nodes['T201'], 'T201:\nNO DISCRETE\nLOG', colors['security'], 13, 7)
draw_node('T202', nodes['T202'], 'T202:\nCOLLISION\nRESISTANT', colors['security'], 13, 7)
draw_node('T203', nodes['T203'], 'T203:\nPERFECT\nZK', colors['security'], 13, 7)
draw_node('T005', nodes['T005'], 'T005:\nPOST-\nQUANTUM', colors['security'], 13, 7)

# Level 4
draw_node('T004', nodes['T004'], 'T004:\n122-BIT\nSOUNDNESS', colors['protocol'], 13, 7)
draw_node('T303', nodes['T303'], 'T303:\nSHA3 GATES\nCORRECT', colors['protocol'], 13, 7)
draw_node('T801', nodes['T801'], 'T801:\nRECURSIVE\nSECURE', colors['protocol'], 13, 7)

# Level 5
draw_node('T150', nodes['T150'], 'T150:\nSUB-200MS\nPROVING', colors['performance'], 14, 7)

# Master
draw_node('MASTER', nodes['MASTER'], 'CIRCULAR\nRECURSION\nWORKS!', colors['master'], 16, 8)

# Draw connections
# From axioms to crypto
draw_arrow('logic', 'info_theory')
draw_arrow('set_theory', 'info_theory')
draw_arrow('peano', 'sha3_foundation')
draw_arrow('field', 'sha3_foundation')

# From crypto to gate axioms
draw_arrow('info_theory', 'A001')
draw_arrow('sha3_foundation', 'A001')
draw_arrow('info_theory', 'A002')

# From gate axioms to security
draw_arrow('A001', 'T201')
draw_arrow('A001', 'T202')
draw_arrow('A002', 'T203')
draw_arrow('T201', 'T005')
draw_arrow('A001', 'T005')

# From security to protocol
draw_arrow('field', 'T004', style='dashed')
draw_arrow('A001', 'T303')
draw_arrow('T004', 'T801')
draw_arrow('T203', 'T801')

# To performance
draw_arrow('T303', 'T150')
draw_arrow('T801', 'T150')

# To master
draw_arrow('T004', 'MASTER')
draw_arrow('T005', 'MASTER')
draw_arrow('T203', 'MASTER')
draw_arrow('T801', 'MASTER')
draw_arrow('T150', 'MASTER')

# Add level labels
levels = [
    (50, 5, 'LEVEL 0: FUNDAMENTAL MATHEMATICAL AXIOMS'),
    (50, 20, 'LEVEL 1: CRYPTOGRAPHIC FOUNDATIONS'),
    (50, 35, 'LEVEL 2: GATE COMPUTER AXIOMS'),
    (50, 50, 'LEVEL 3: SECURITY PROPERTIES'),
    (50, 65, 'LEVEL 4: PROTOCOL PROPERTIES'),
    (50, 80, 'LEVEL 5: PERFORMANCE'),
    (50, 95, 'MASTER TRUTH')
]

for x, y, label in levels:
    ax.text(x, y, label, ha='center', va='center',
            fontsize=12, fontweight='bold', style='italic')

# Add title
ax.text(50, 130, 'GATE COMPUTER TRUTH DEPENDENCY TREE', 
        ha='center', va='center', fontsize=20, fontweight='bold')
ax.text(50, 125, 'From Mathematical Axioms to Circular Recursion', 
        ha='center', va='center', fontsize=14, style='italic')

# Add legend box
legend_items = [
    ('Mathematical Axioms', colors['axiom']),
    ('Cryptographic Foundations', colors['crypto']),
    ('Gate Computer Axioms', colors['gate']),
    ('Security Properties', colors['security']),
    ('Protocol Properties', colors['protocol']),
    ('Performance', colors['performance']),
    ('Master Truth', colors['master'])
]

legend_x = 85
legend_y = 115
for i, (label, color) in enumerate(legend_items):
    y = legend_y - i * 3
    rect = patches.Rectangle((legend_x, y), 3, 2, facecolor=color, edgecolor='black')
    ax.add_patch(rect)
    ax.text(legend_x + 4, y + 1, label, va='center', fontsize=9)

# Add key insights
insights_text = """KEY INSIGHTS:
• Every truth traces back to mathematical axioms
• A001 (SHA3-only) and A002 (ZK-always) are the foundation
• T004 (122-bit soundness) comes from GF(2^128) field theory
• All properties combine to enable circular recursion
• The system is provably secure and performant"""

ax.text(5, 120, insights_text, fontsize=10, 
        bbox=dict(boxstyle="round,pad=0.5", facecolor='lightgray'))

plt.tight_layout()
plt.savefig('/home/bob/github/gate_computer/truth_dependency_tree.png', dpi=300, bbox_inches='tight')
plt.savefig('/home/bob/github/gate_computer/truth_dependency_tree.pdf', bbox_inches='tight')
print("Truth dependency tree saved as truth_dependency_tree.png and .pdf")