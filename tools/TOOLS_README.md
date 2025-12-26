# Gate Computer Tools

This directory contains various tools and utilities for working with the Gate Computer proof system.

## 🛠️ Tool Categories

### Performance Analysis
- `basefold_cpu_profiler.c` - CPU profiling for BaseFold operations
- `cache_optimization_detective.c` - Cache performance analysis
- `memory_bandwidth_optimizer.c` - Memory bandwidth optimization
- `proving_time_*` - Various proving time analysis tools
- `recursive_proof_benchmark*.c` - Recursive proof benchmarking

### Security Analysis
- `security_*_analysis.c` - Security analysis at different bit levels
- `security_equivalence_proof.c` - Prove security equivalence
- `query_correlation_proof_verification.c` - Verify query correlations

### Truth System
- `truth_detective.c` - Analyze truth statements
- `truth_score_tracker.c` - Track truth verification scores
- `truth_debate_*.py` - Truth debate simulation tools
- `verify_truth_evidence.c` - Evidence verification
- `proof_status_reporter.c` - Report proof coverage status

### Proof Tools
- `proof_dependency_map.py` - Visualize proof dependencies
- `generate_proof_graph.py` - Create proof dependency graphs
- `fopl_*.py` - First-order logic proof tools

### Circuit Generation
- `bitcoin_circuit_*.c` - Bitcoin circuit generators
- `chess_circuit_*.c` - Chess verification circuits
- `secp256k1_circuit_generator.c` - Elliptic curve circuits
- `sha256_circuit_generator.c` - SHA256 circuit generation

### Optimization Research
- `algebraic_optimization_explorer.c` - Explore algebraic optimizations
- `recursive_optimization_*.c` - Recursive proof optimizations
- `sub_second_*.c` - Sub-second proof optimization research

### Testing & Debugging
- `test_*.c` - Various test programs
- `debug_*.c` - Debugging utilities
- `minimal_*.c` - Minimal test cases

### BaseFold Specific
- `basefold_verifier_*.c` - BaseFold verifier circuit tools
- `basefold_tensor_structure_analysis.c` - Tensor structure analysis
- `basefold_implementation_investigation.c` - Implementation analysis

### Documentation Generation
- `generate_readable_proofs.py` - Generate human-readable proofs
- `wip_truth_generator.py` - Generate work-in-progress truths

## 📚 Usage Examples

### Performance Analysis
```bash
# Profile CPU usage
gcc -O3 tools/basefold_cpu_profiler.c -o cpu_profiler
./cpu_profiler

# Analyze cache performance
gcc -O3 tools/cache_optimization_detective.c -o cache_detective
./cache_detective
```

### Truth Verification
```bash
# Check proof dependencies
python3 tools/proof_dependency_map.py

# Generate proof status report
gcc tools/proof_status_reporter.c -o proof_reporter -ltruth_verifier -lm
./proof_reporter
```

### Circuit Generation
```bash
# Generate SHA256 circuit
gcc tools/sha256_circuit_generator.c -o sha256_gen
./sha256_gen > sha256_circuit.txt
```

## 🔧 Building Tools

Most tools can be built with:
```bash
gcc -O3 tools/TOOL_NAME.c -o TOOL_NAME -I modules/*/include -L build/lib -lbasefold_raa -lgf128 -lsha3 -lm
```

Some tools require additional libraries:
- Truth tools: `-ltruth_verifier`
- Circuit tools: `-lcircuit_generator`
- Python tools: Require Python 3.6+

## 📝 Contributing

When adding new tools:
1. Use descriptive names indicating the tool's purpose
2. Add a header comment explaining what the tool does
3. Update this README with the new tool
4. Follow the existing code style

## ⚠️ Note

Many tools in this directory are for research and testing purposes. Production-ready utilities should be promoted to the main binary or appropriate modules.