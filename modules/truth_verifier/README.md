# Truth Verifier Module

A minimal implementation of the Truth Bucket System for gate_computer that captures and validates facts about the codebase through programmatic verification.

## Overview

The Truth Bucket System organizes knowledge about gate_computer into five categories:

1. **TRUTH (T###)** - Verified facts with programmatic checks
2. **FALSE (F###)** - Common misconceptions verified as false
3. **DERIVED (D###)** - Logical deductions from base truths
4. **UNCERTAIN (U###)** - Questions requiring investigation
5. **PHILOSOPHICAL (P###)** - Domain-level principles

## Usage

```bash
# Verify all truths
./verify_truths.sh

# Verbose output with details
./verify_truths.sh --verbose

# Verify specific truth
./verify_truths.sh --id T004

# List all registered truths
./verify_truths.sh --list

# Generate report
./verify_truths.sh --report truth_report.txt
```

## Example Truths

Currently registered truths include:

- **T001**: SHA3-256 circuit has 192,086 gates
- **T004**: Effective soundness is 122 bits (not 128) due to sumcheck limitations
- **F001**: System claims 128-bit soundness (FALSE - it's 122-bit)
- **F701**: Truth City viewer exists (FALSE - it was removed)
- **D001**: Average gates per SHA3 round = 192,086 / 24 ≈ 8,003
- **P001**: Every computation can be represented as a circuit

## Adding New Truths

To add new truths, edit `src/gate_computer_truths.c`:

```c
static truth_result_t verify_T005_new_truth(char *details, size_t size) {
    // Verification logic
    if (condition_is_true) {
        snprintf(details, size, "Evidence: %s", evidence);
        return TRUTH_VERIFIED;
    }
    return TRUTH_FAILED;
}

// In register_gate_computer_truths():
{
    .id = "T005",
    .type = BUCKET_TRUTH,
    .statement = "New truth statement",
    .category = "category",
    .verify = verify_T005_new_truth
}
```

## Benefits

- **Living Documentation** - Always synchronized with code
- **Regression Prevention** - Catch breaking changes
- **Knowledge Preservation** - Capture institutional knowledge
- **Onboarding Tool** - New developers learn verified facts
- **Debugging Aid** - Check assumptions when things fail

## Implementation Details

The verifier performs simple checks including:
- File existence verification
- String searches in source files
- Mathematical calculations
- Build configuration checks
- Documentation validation

Each truth can return one of four states:
- `TRUTH_VERIFIED` - Successfully verified
- `TRUTH_FAILED` - Verification failed
- `TRUTH_UNCERTAIN` - Cannot determine
- `TRUTH_NOT_APPLICABLE` - Not relevant in context

## Future Extensions

The system is designed to be extensible:
- Add more sophisticated verification logic
- Integrate with test results
- Generate documentation automatically
- Create dependency graphs between truths
- Export to different formats (JSON, HTML, etc.)