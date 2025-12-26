/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/stat.h>
#include <unistd.h>

#define MAX_TRUTHS 1000
#define MAX_LINE 1024
#define CACHE_DIR ".truth_cache"
#define SCORE_FILE ".truth_cache/current_score.txt"
#define HISTORY_FILE ".truth_cache/history.csv"

typedef enum {
    STATE_VERIFIED,
    STATE_FAILED,
    STATE_UNCERTAIN,
    STATE_NOT_APPLICABLE
} truth_state_t;

typedef struct {
    char id[16];
    char type[16];
    truth_state_t state;
    char statement[256];
    int weight;  // Importance weight (1-10)
} truth_entry_t;

typedef struct {
    int total_truths;
    int verified;
    int failed;
    int uncertain;
    int not_applicable;
    double score;
    time_t timestamp;
    truth_entry_t truths[MAX_TRUTHS];
} truth_snapshot_t;

// Weight assignments for different truth types
int get_truth_weight(const char *id) {
    if (strncmp(id, "T2", 2) == 0) return 10;  // Security truths are critical
    if (strncmp(id, "T1", 2) == 0) return 8;   // Performance truths are important
    if (strncmp(id, "T3", 2) == 0) return 6;   // Implementation truths
    if (strncmp(id, "P", 1) == 0) return 4;    // Philosophical truths
    if (strncmp(id, "D", 1) == 0) return 3;    // Derived truths
    if (strncmp(id, "F", 1) == 0) return 7;    // False beliefs (important to verify)
    if (strncmp(id, "U", 1) == 0) return 2;    // Uncertain (low weight)
    return 5;  // Default
}

// Calculate score based on truth states and weights
double calculate_score(truth_snapshot_t *snapshot) {
    double total_weight = 0;
    double achieved_weight = 0;
    
    for (int i = 0; i < snapshot->total_truths; i++) {
        truth_entry_t *truth = &snapshot->truths[i];
        total_weight += truth->weight;
        
        // For TRUTH types, verified is good
        if (strcmp(truth->type, "TRUTH") == 0 && truth->state == STATE_VERIFIED) {
            achieved_weight += truth->weight;
        }
        // For FALSE types, verified means correctly identified as false (good)
        else if (strcmp(truth->type, "FALSE") == 0 && truth->state == STATE_VERIFIED) {
            achieved_weight += truth->weight;
        }
        // For DERIVED types, verified is good
        else if (strcmp(truth->type, "DERIVED") == 0 && truth->state == STATE_VERIFIED) {
            achieved_weight += truth->weight;
        }
        // For PHILOSOPHICAL types, verified is good
        else if (strcmp(truth->type, "PHILOSOPHICAL") == 0 && truth->state == STATE_VERIFIED) {
            achieved_weight += truth->weight;
        }
        // For UNCERTAIN types, we expect them to be uncertain (neutral)
        else if (strcmp(truth->type, "UNCERTAIN") == 0) {
            achieved_weight += truth->weight * 0.5;  // Half credit for known unknowns
        }
    }
    
    return (achieved_weight / total_weight) * 100.0;
}

// Parse truth verifier output
truth_snapshot_t* parse_verifier_output(FILE *fp) {
    truth_snapshot_t *snapshot = calloc(1, sizeof(truth_snapshot_t));
    if (!snapshot) return NULL;
    
    char line[MAX_LINE];
    int truth_count = 0;
    
    while (fgets(line, sizeof(line), fp)) {
        // Parse truth entries
        if (line[0] == '[') {
            char id[16], type[32];
            char state_symbol;
            
            // Extract ID
            char *id_start = strchr(line, '[') + 1;
            char *id_end = strchr(line, ']');
            if (!id_start || !id_end) continue;
            
            int id_len = id_end - id_start;
            strncpy(id, id_start, id_len);
            id[id_len] = '\0';
            
            // Extract state symbol
            state_symbol = line[id_end - line + 2];
            
            // Extract type
            char *type_start = strstr(line, "(");
            char *type_end = strstr(line, ")");
            if (type_start && type_end) {
                int type_len = type_end - type_start - 1;
                strncpy(type, type_start + 1, type_len);
                type[type_len] = '\0';
            }
            
            // Extract statement
            char *statement_start = strstr(line, "Statement: ");
            char statement[256] = "";
            if (statement_start) {
                statement_start += strlen("Statement: ");
                strncpy(statement, statement_start, sizeof(statement) - 1);
                // Remove newline
                char *nl = strchr(statement, '\n');
                if (nl) *nl = '\0';
            }
            
            // Set entry data
            truth_entry_t *entry = &snapshot->truths[truth_count];
            strcpy(entry->id, id);
            strcpy(entry->type, type);
            strcpy(entry->statement, statement);
            entry->weight = get_truth_weight(id);
            
            // Set state based on symbol or UTF-8 sequence
            if (state_symbol == '?' || strncmp(&line[id_end - line + 2], "?", 1) == 0) {
                entry->state = STATE_UNCERTAIN;
                snapshot->uncertain++;
            } else if (state_symbol == '-') {
                entry->state = STATE_NOT_APPLICABLE;
                snapshot->not_applicable++;
            } else if (strncmp(&line[id_end - line + 2], "✓", 3) == 0) {
                entry->state = STATE_VERIFIED;
                snapshot->verified++;
            } else if (strncmp(&line[id_end - line + 2], "✗", 3) == 0) {
                entry->state = STATE_FAILED;
                snapshot->failed++;
            } else {
                // Default to uncertain if can't determine
                entry->state = STATE_UNCERTAIN;
                snapshot->uncertain++;
            }
            
            truth_count++;
        }
        
        // Parse summary
        if (strstr(line, "Total registered truths:")) {
            sscanf(line, "Total registered truths: %d", &snapshot->total_truths);
        }
    }
    
    snapshot->timestamp = time(NULL);
    snapshot->score = calculate_score(snapshot);
    
    return snapshot;
}

// Save snapshot to cache
void save_snapshot(truth_snapshot_t *snapshot) {
    // Create cache directory if it doesn't exist
    mkdir(CACHE_DIR, 0755);
    
    // Save current score
    FILE *fp = fopen(SCORE_FILE, "w");
    if (fp) {
        fprintf(fp, "%.2f\n", snapshot->score);
        fprintf(fp, "%ld\n", snapshot->timestamp);
        fprintf(fp, "Verified: %d\n", snapshot->verified);
        fprintf(fp, "Failed: %d\n", snapshot->failed);
        fprintf(fp, "Uncertain: %d\n", snapshot->uncertain);
        fprintf(fp, "Total: %d\n", snapshot->total_truths);
        fclose(fp);
    }
    
    // Append to history
    fp = fopen(HISTORY_FILE, "a");
    if (fp) {
        // Add header if file is new
        struct stat st;
        if (stat(HISTORY_FILE, &st) == 0 && st.st_size == 0) {
            fprintf(fp, "timestamp,score,verified,failed,uncertain,total\n");
        }
        
        fprintf(fp, "%ld,%.2f,%d,%d,%d,%d\n",
                snapshot->timestamp, snapshot->score,
                snapshot->verified, snapshot->failed,
                snapshot->uncertain, snapshot->total_truths);
        fclose(fp);
    }
    
    // Save detailed state
    char state_file[256];
    snprintf(state_file, sizeof(state_file), "%s/state_%ld.txt", CACHE_DIR, snapshot->timestamp);
    fp = fopen(state_file, "w");
    if (fp) {
        for (int i = 0; i < snapshot->total_truths; i++) {
            truth_entry_t *t = &snapshot->truths[i];
            fprintf(fp, "%s|%s|%d|%d|%s\n", 
                    t->id, t->type, t->state, t->weight, t->statement);
        }
        fclose(fp);
    }
}

// Display score report
void display_report(truth_snapshot_t *snapshot) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║                    TRUTH SCORE REPORT                            ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║  Overall Score: %6.2f%%                                         ║\n", snapshot->score);
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║  ✓ Verified:        %3d                                          ║\n", snapshot->verified);
    printf("║  ✗ Failed:          %3d                                          ║\n", snapshot->failed);
    printf("║  ? Uncertain:       %3d                                          ║\n", snapshot->uncertain);
    printf("║  - Not Applicable:  %3d                                          ║\n", snapshot->not_applicable);
    printf("║  ─────────────────────                                           ║\n");
    printf("║  Total Truths:      %3d                                          ║\n", snapshot->total_truths);
    printf("╚══════════════════════════════════════════════════════════════════╝\n");
    
    // Show critical failures
    printf("\nCritical Issues (High-weight failures):\n");
    int critical_count = 0;
    for (int i = 0; i < snapshot->total_truths; i++) {
        truth_entry_t *t = &snapshot->truths[i];
        if (t->weight >= 8 && 
            ((strcmp(t->type, "TRUTH") == 0 && t->state != STATE_VERIFIED) ||
             (strcmp(t->type, "FALSE") == 0 && t->state != STATE_VERIFIED))) {
            printf("  ⚠ %s: %s\n", t->id, t->statement);
            critical_count++;
        }
    }
    if (critical_count == 0) {
        printf("  ✓ No critical issues found!\n");
    }
    
    // Score interpretation
    printf("\nScore Interpretation:\n");
    if (snapshot->score >= 95.0) {
        printf("  🏆 EXCELLENT - System is in optimal state\n");
    } else if (snapshot->score >= 85.0) {
        printf("  ✅ GOOD - System is healthy with minor issues\n");
    } else if (snapshot->score >= 70.0) {
        printf("  ⚠️  FAIR - System needs attention\n");
    } else {
        printf("  ❌ POOR - System has significant issues\n");
    }
    
    char time_str[64];
    strftime(time_str, sizeof(time_str), "%Y-%m-%d %H:%M:%S", localtime(&snapshot->timestamp));
    printf("\nGenerated: %s\n", time_str);
}

// Compare with previous snapshot
void show_changes(truth_snapshot_t *current) {
    char prev_file[256];
    snprintf(prev_file, sizeof(prev_file), "%s/previous_score.txt", CACHE_DIR);
    
    FILE *fp = fopen(prev_file, "r");
    if (fp) {
        double prev_score;
        long prev_time;
        if (fscanf(fp, "%lf\n%ld\n", &prev_score, &prev_time) == 2) {
            double delta = current->score - prev_score;
            printf("\nScore Change: %.2f%% → %.2f%% (%+.2f%%)\n", 
                   prev_score, current->score, delta);
            
            if (delta > 0) {
                printf("📈 Improvement detected!\n");
            } else if (delta < 0) {
                printf("📉 Regression detected - investigate changes\n");
            } else {
                printf("➡️  No change in score\n");
            }
        }
        fclose(fp);
    }
    
    // Save current as previous for next run
    rename(SCORE_FILE, prev_file);
}

int main(int argc, char *argv[]) {
    int show_details = 0;
    int continuous = 0;
    
    // Parse arguments
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--details") == 0 || strcmp(argv[i], "-d") == 0) {
            show_details = 1;
        } else if (strcmp(argv[i], "--continuous") == 0 || strcmp(argv[i], "-c") == 0) {
            continuous = 1;
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            printf("Truth Score Tracker - Monitor Gate Computer truth verification scores\n");
            printf("\nUsage: %s [options]\n", argv[0]);
            printf("\nOptions:\n");
            printf("  -d, --details     Show detailed truth states\n");
            printf("  -c, --continuous  Run continuously (every 60 seconds)\n");
            printf("  -h, --help        Show this help\n");
            return 0;
        }
    }
    
    do {
        // Run truth verifier and capture output
        FILE *fp = popen("./verify_truths.sh 2>&1", "r");
        if (!fp) {
            fprintf(stderr, "Error: Could not run truth verifier\n");
            return 1;
        }
        
        truth_snapshot_t *snapshot = parse_verifier_output(fp);
        pclose(fp);
        
        if (!snapshot) {
            fprintf(stderr, "Error: Could not parse verifier output\n");
            return 1;
        }
        
        // Display report
        display_report(snapshot);
        
        // Show changes
        show_changes(snapshot);
        
        // Save snapshot
        save_snapshot(snapshot);
        
        // Show details if requested
        if (show_details) {
            printf("\n\nDetailed Truth States:\n");
            printf("%-6s %-15s %-10s %-6s %s\n", "ID", "Type", "State", "Weight", "Statement");
            printf("%-6s %-15s %-10s %-6s %s\n", "──────", "───────────────", "──────────", "──────", "─────────");
            
            for (int i = 0; i < snapshot->total_truths; i++) {
                truth_entry_t *t = &snapshot->truths[i];
                const char *state_str[] = {"VERIFIED", "FAILED", "UNCERTAIN", "N/A"};
                printf("%-6s %-15s %-10s %-6d %.60s%s\n", 
                       t->id, t->type, state_str[t->state], t->weight,
                       t->statement, strlen(t->statement) > 60 ? "..." : "");
            }
        }
        
        free(snapshot);
        
        if (continuous) {
            printf("\n\nNext check in 60 seconds... (Press Ctrl+C to stop)\n");
            sleep(60);
            system("clear");
        }
    } while (continuous);
    
    return 0;
}