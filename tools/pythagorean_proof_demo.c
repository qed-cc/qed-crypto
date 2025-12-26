/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>

int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║     PYTHAGOREAN THEOREM: FROM AXIOMS TO PROOF                ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");
    
    printf("📐 THE THEOREM: For a right triangle, a² + b² = c²\n\n");
    
    printf("🏛️ AXIOM FOUNDATION:\n");
    printf("════════════════════\n\n");
    
    printf("LEVEL 0: LOGIC\n");
    printf("──────────────\n");
    printf("• Law of Identity: A = A\n");
    printf("• Law of Non-contradiction: ¬(P ∧ ¬P)\n");
    printf("• Modus Ponens: P, P→Q ⊢ Q\n\n");
    
    printf("LEVEL 1: PEANO AXIOMS (Natural Numbers)\n");
    printf("────────────────────────────────────────\n");
    printf("• PA1: 0 is a natural number\n");
    printf("• PA2: If n is natural, then S(n) is natural\n");
    printf("• PA3: 0 is not the successor of any number\n");
    printf("• PA4: Different numbers have different successors\n");
    printf("• PA5: Induction principle\n\n");
    
    printf("LEVEL 2: FIELD AXIOMS (Arithmetic)\n");
    printf("───────────────────────────────────\n");
    printf("• Closure: a+b and a×b are numbers\n");
    printf("• Associativity: (a+b)+c = a+(b+c)\n");
    printf("• Commutativity: a+b = b+a, a×b = b×a\n");
    printf("• Identity: a+0 = a, a×1 = a\n");
    printf("• Distributivity: a×(b+c) = a×b + a×c\n\n");
    
    printf("LEVEL 3: EUCLIDEAN AXIOMS (Geometry)\n");
    printf("─────────────────────────────────────\n");
    printf("• E1: A line through any two points\n");
    printf("• E2: Any line segment can be extended\n");
    printf("• E3: A circle with any center and radius\n");
    printf("• E4: All right angles are equal\n");
    printf("• E5: Parallel postulate\n\n");
    
    printf("LEVEL 4: COORDINATE GEOMETRY\n");
    printf("─────────────────────────────\n");
    printf("• Points: P = (x, y) where x,y ∈ ℝ\n");
    printf("• Distance: d² = (x₂-x₁)² + (y₂-y₁)²\n");
    printf("• Vectors: v = (dx, dy)\n");
    printf("• Dot product: v₁·v₂ = dx₁×dx₂ + dy₁×dy₂\n");
    printf("• Perpendicular: v₁⊥v₂ ⟺ v₁·v₂ = 0\n\n");
    
    printf("🎯 THE PROOF:\n");
    printf("══════════════\n\n");
    
    printf("Given: Triangle ABC with right angle at B\n");
    printf("Prove: |AC|² = |AB|² + |BC|²\n\n");
    
    printf("Step 1: Express vectors\n");
    printf("  →AB = B - A = (b_x - a_x, b_y - a_y)\n");
    printf("  →BC = C - B = (c_x - b_x, c_y - b_y)\n");
    printf("  →AC = C - A = (c_x - a_x, c_y - a_y)\n\n");
    
    printf("Step 2: Note that →AC = →AB + →BC (vector addition)\n\n");
    
    printf("Step 3: Calculate |AC|²\n");
    printf("  |AC|² = |→AB + →BC|²\n");
    printf("        = (→AB + →BC)·(→AB + →BC)\n");
    printf("        = →AB·→AB + 2(→AB·→BC) + →BC·→BC\n");
    printf("        = |AB|² + 2(→AB·→BC) + |BC|²\n\n");
    
    printf("Step 4: Use the right angle condition\n");
    printf("  Since angle ABC = 90°, →AB ⊥ →BC\n");
    printf("  Therefore: →AB·→BC = 0\n\n");
    
    printf("Step 5: Conclude\n");
    printf("  |AC|² = |AB|² + 0 + |BC|²\n");
    printf("  |AC|² = |AB|² + |BC|² ✓\n\n");
    
    printf("📊 EXAMPLE: The 3-4-5 Triangle\n");
    printf("════════════════════════════════\n");
    printf("A = (0,0), B = (3,0), C = (3,4)\n\n");
    printf("→AB = (3,0), |AB|² = 9\n");
    printf("→BC = (0,4), |BC|² = 16\n");
    printf("→AC = (3,4), |AC|² = 25\n\n");
    printf("Verify: →AB·→BC = 3×0 + 0×4 = 0 ✓ (perpendicular)\n");
    printf("Verify: 9 + 16 = 25 ✓\n\n");
    
    printf("💡 THE DEEP INSIGHT:\n");
    printf("════════════════════\n");
    printf("The Pythagorean theorem emerges from the interplay of:\n");
    printf("• ALGEBRA (field operations, distributivity)\n");
    printf("• GEOMETRY (distance, angles, perpendicularity)\n");
    printf("• The key: perpendicular vectors have zero dot product!\n\n");
    
    printf("This is why right triangles are special - the cross-terms vanish,\n");
    printf("leaving us with the beautiful equation: a² + b² = c²\n\n");
    
    return 0;
}