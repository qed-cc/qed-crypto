# Truth Challenge Game - "This is TRUE CHANGE MY MIND"

A Bret Victor style interactive game where you challenge the mathematical foundations of the BaseFold RAA proof system.

## Overview

This is a native WebView application (not a browser game) that presents the complete truth dependency tree of our proof system. Players navigate from fundamental mathematical axioms up to the master claim that "Circular Recursion Works", attempting to find logical flaws.

## Building

```bash
cd apps/truth_challenge_game
make
```

## Running

```bash
./truth_challenge_game
```

Or from project root:
```bash
./apps/truth_challenge_game/truth_challenge_game
```

## Gameplay

- **Start**: Level 0 with mathematical axioms (100% confidence)
- **Goal**: Reduce confidence below 50% to "win"
- **Mechanics**: 
  - Click truth nodes to examine them
  - Click "I Disagree" to challenge
  - Claude defends with mathematical arguments
  - Each maintained dispute reduces confidence by 5%

## Features

- Native GTK/WebKit window (1400x900)
- No external dependencies (HTML embedded)
- Real-time stats tracking
- 20+ truth nodes across 7 levels
- Intelligent Claude responses
- Keyboard shortcuts (ESC to close)

## Truth Levels

0. **Mathematical Axioms** - ZFC, GF(2), Boolean algebra
1. **Field Theory** - Polynomial rings, irreducibility  
2. **Cryptographic Primitives** - Gates, constraints, SHA3
3. **Protocol Properties** - Soundness bounds, zero-sum
4. **Composition Theorems** - Recursion soundness
5. **Recursive Constructions** - Fixed points
6. **Master Proof** - Circular recursion works

## Strategy Tips

- Attack foundational truths for maximum impact
- Question the 121-bit soundness (not 128!)
- Challenge polynomial irreducibility
- Dispute the 30M gate verifier size
- Find contradictions in circular reasoning