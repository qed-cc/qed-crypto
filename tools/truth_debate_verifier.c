/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <time.h>

typedef struct {
    const char* truth_id;
    const char* statement;
    double openai_confidence;
    double claude_confidence;
    double consensus_confidence;
    int passes_99_percent;
} debate_result_t;

typedef struct {
    const char* truth_id;
    const char* statement;
    const char* category;
    const char* evidence[10];  // Up to 10 evidence points
    int evidence_count;
} truth_claim_t;

// Truth claims to debate
static const truth_claim_t TRUTH_CLAIMS[] = {
    {
        .truth_id = "T001",
        .statement = "Gate Computer is a zero-knowledge proof system implementation",
        .category = "Identity",
        .evidence = {
            "AXIOM A002: All proofs MUST be zero-knowledge (enable_zk = 1 ALWAYS)",
            "Polynomial masking implementation in polynomial_zk_field_masking.c",
            "Fiat-Shamir transform for non-interactive ZK",
            "Information-theoretic security: masked polynomials reveal nothing",
            NULL
        },
        .evidence_count = 4
    },
    {
        .truth_id = "T004", 
        .statement = "The system achieves 122-bit security level",
        .category = "Security",
        .evidence = {
            "Schwartz-Zippel lemma: P(cheating) ≤ nd/|F| = 54/2^128",
            "18 sumcheck rounds × degree 3 = 54 bits lost",
            "Exact calculation: 2^(-122.58) soundness error",
            "Post-quantum secure - no discrete log assumptions",
            NULL
        },
        .evidence_count = 4
    },
    {
        .truth_id = "T006",
        .statement = "SHA3-256 is used for all hashing operations", 
        .category = "Cryptography",
        .evidence = {
            "AXIOM A001: Only SHA3 allowed (ALL others BANNED)",
            "Keccak-f[1600] permutation with 24 rounds",
            "No other hash functions linked in binary",
            "Compile-time enforcement - build fails without SHA3",
            NULL
        },
        .evidence_count = 4
    },
    {
        .truth_id = "T012",
        .statement = "Proof size is approximately 9KB",
        .category = "Memory",
        .evidence = {
            "ACTUAL SIZE: ~190KB measured empirically",
            "Merkle tree commitments: 128KB",
            "Sumcheck messages: 48KB",
            "9KB was theoretical target, not reality",
            NULL
        },
        .evidence_count = 4
    }
};

#define NUM_TRUTHS (sizeof(TRUTH_CLAIMS) / sizeof(TRUTH_CLAIMS[0]))

static void print_banner(void) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║            FORMAL TRUTH DEBATE VERIFICATION SYSTEM               ║\n");
    printf("║         Using OpenAI GPT-4 + Claude for 99%% Confidence          ║\n");
    printf("╚══════════════════════════════════════════════════════════════════╝\n");
    printf("\n");
}

static int check_openai_key(void) {
    const char* api_key = getenv("OPENAI_API_KEY");
    if (!api_key || strlen(api_key) == 0) {
        fprintf(stderr, "ERROR: OPENAI_API_KEY environment variable not set\n");
        fprintf(stderr, "Please run: export OPENAI_API_KEY='your-key-here'\n");
        return 0;
    }
    return 1;
}

static int run_python_debate(const char* truth_id) {
    char cmd[1024];
    snprintf(cmd, sizeof(cmd), 
        "cd /home/bob/github/gate_computer && "
        "python3 -c \""
        "import sys; sys.path.append('tools'); "
        "from truth_debate_system import TruthDebateSystem; "
        "system = TruthDebateSystem(); "
        "result = system.conduct_debate('%s', rounds=3); "
        "print(f'{result.truth_id}|{result.openai_confidence}|{result.claude_confidence}|{result.consensus_confidence}|{int(result.consensus_confidence >= 99.0)}')\"",
        truth_id);
    
    FILE* fp = popen(cmd, "r");
    if (!fp) {
        fprintf(stderr, "Failed to run debate for %s\n", truth_id);
        return -1;
    }
    
    char buffer[512];
    debate_result_t result = {0};
    
    while (fgets(buffer, sizeof(buffer), fp)) {
        // Look for result line
        if (strstr(buffer, truth_id) && strchr(buffer, '|')) {
            char* token = strtok(buffer, "|");
            if (token) result.truth_id = truth_id;
            
            token = strtok(NULL, "|");
            if (token) result.openai_confidence = atof(token);
            
            token = strtok(NULL, "|");
            if (token) result.claude_confidence = atof(token);
            
            token = strtok(NULL, "|");
            if (token) result.consensus_confidence = atof(token);
            
            token = strtok(NULL, "|");
            if (token) result.passes_99_percent = atoi(token);
        }
    }
    
    int status = pclose(fp);
    
    // Print results
    printf("\n┌─────────────────────────────────────────────────────────────┐\n");
    printf("│ DEBATE RESULT: %s                                          │\n", truth_id);
    printf("├─────────────────────────────────────────────────────────────┤\n");
    printf("│ OpenAI Confidence:  %6.2f%%                                │\n", result.openai_confidence);
    printf("│ Claude Confidence:  %6.2f%%                                │\n", result.claude_confidence);
    printf("│ Consensus:          %6.2f%%                                │\n", result.consensus_confidence);
    printf("│ Status: %s │\n", 
        result.passes_99_percent ? "✓ PASSES 99% THRESHOLD                      " : 
                                  "✗ FAILS 99% THRESHOLD                       ");
    printf("└─────────────────────────────────────────────────────────────┘\n");
    
    return result.passes_99_percent ? 0 : 1;
}

static void generate_fopl_proof(const truth_claim_t* claim) {
    printf("\n=== FIRST-ORDER LOGIC FOUNDATION ===\n");
    printf("Claim: %s\n", claim->statement);
    printf("\nFormal structure:\n");
    printf("∀x(TruthClaim(x) → ∃d∃c(Debate(d,x) ∧ Confidence(c,d) ∧ c ≥ 0.99))\n");
    printf("TruthClaim(%s)\n", claim->truth_id);
    printf("Evidence predicates:\n");
    
    for (int i = 0; i < claim->evidence_count && claim->evidence[i]; i++) {
        printf("  E%d: %s\n", i+1, claim->evidence[i]);
    }
}

int main(int argc, char* argv[]) {
    print_banner();
    
    // Check for API key
    if (!check_openai_key()) {
        return 1;
    }
    
    // Track results
    int total_truths = 0;
    int high_confidence_truths = 0;
    int failed_truths = 0;
    
    printf("Starting formal debates for %zu truth claims...\n", NUM_TRUTHS);
    printf("Each claim will be debated with pro/con arguments.\n");
    printf("Target: 99%% confidence after hearing counterarguments.\n\n");
    
    // Process specific truth or all
    if (argc > 1 && strncmp(argv[1], "T", 1) == 0) {
        // Debate specific truth
        for (size_t i = 0; i < NUM_TRUTHS; i++) {
            if (strcmp(TRUTH_CLAIMS[i].truth_id, argv[1]) == 0) {
                printf("Debating %s: %s\n", 
                    TRUTH_CLAIMS[i].truth_id, 
                    TRUTH_CLAIMS[i].statement);
                
                generate_fopl_proof(&TRUTH_CLAIMS[i]);
                
                int result = run_python_debate(TRUTH_CLAIMS[i].truth_id);
                if (result == 0) high_confidence_truths++;
                else failed_truths++;
                total_truths++;
                break;
            }
        }
    } else {
        // Debate all truths
        for (size_t i = 0; i < NUM_TRUTHS; i++) {
            printf("\n[%zu/%zu] Debating %s: %s\n", 
                i+1, NUM_TRUTHS,
                TRUTH_CLAIMS[i].truth_id, 
                TRUTH_CLAIMS[i].statement);
            
            generate_fopl_proof(&TRUTH_CLAIMS[i]);
            
            int result = run_python_debate(TRUTH_CLAIMS[i].truth_id);
            if (result == 0) high_confidence_truths++;
            else failed_truths++;
            total_truths++;
            
            // Rate limiting
            if (i < NUM_TRUTHS - 1) {
                printf("\nWaiting before next debate...\n");
                sleep(2);
            }
        }
    }
    
    // Final summary
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║                      FINAL SUMMARY                               ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║ Total Truth Claims Debated: %-36d ║\n", total_truths);
    printf("║ Passed 99%% Confidence:      %-36d ║\n", high_confidence_truths);
    printf("║ Failed 99%% Confidence:      %-36d ║\n", failed_truths);
    printf("║ Success Rate:               %-35.1f%% ║\n", 
        total_truths > 0 ? (100.0 * high_confidence_truths / total_truths) : 0.0);
    printf("╚══════════════════════════════════════════════════════════════════╝\n");
    
    if (high_confidence_truths == total_truths) {
        printf("\n✓ ALL TRUTHS MAINTAIN 99%% CONFIDENCE AFTER RIGOROUS DEBATE!\n");
        return 0;
    } else {
        printf("\n✗ Some truths failed to maintain 99%% confidence.\n");
        printf("  Review and strengthen the evidence for failed claims.\n");
        return 1;
    }
}