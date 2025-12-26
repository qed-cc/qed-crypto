/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include <getopt.h>

static pid_t server_pid = 0;

void cleanup_server(int sig) {
    if (server_pid > 0) {
        printf("\nStopping game server...\n");
        kill(server_pid, SIGTERM);
        waitpid(server_pid, NULL, 0);
    }
    exit(0);
}

void print_usage(const char *prog_name) {
    printf("Usage: %s [OPTIONS]\n", prog_name);
    printf("\nOptions:\n");
    printf("  -h, --help     Show this help message\n");
    printf("  -g, --game     Launch the interactive game view (default: list view)\n");
    printf("  -l, --list     Launch the list view (default)\n");
    printf("\n");
}

void print_ascii_logo() {
    printf("\033[2J\033[H"); // Clear screen
    printf("\033[32m"); // Green text
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║                                                                      ║\n");
    printf("║  ████████╗██╗  ██╗██╗███████╗    ██╗███████╗    ████████╗██████╗   ║\n");
    printf("║  ╚══██╔══╝██║  ██║██║██╔════╝    ██║██╔════╝    ╚══██╔══╝██╔══██╗  ║\n");
    printf("║     ██║   ███████║██║███████╗    ██║███████╗       ██║   ██████╔╝  ║\n");
    printf("║     ██║   ██╔══██║██║╚════██║    ██║╚════██║       ██║   ██╔══██╗  ║\n");
    printf("║     ██║   ██║  ██║██║███████║    ██║███████║       ██║   ██║  ██║  ║\n");
    printf("║     ╚═╝   ╚═╝  ╚═╝╚═╝╚══════╝    ╚═╝╚══════╝       ╚═╝   ╚═╝  ╚═╝  ║\n");
    printf("║                                                                      ║\n");
    printf("║            ██╗   ██╗███████╗                                         ║\n");
    printf("║            ██║   ██║██╔════╝                                         ║\n");
    printf("║            ██║   ██║█████╗                                           ║\n");
    printf("║            ██║   ██║██╔══╝                                           ║\n");
    printf("║            ╚██████╔╝███████╗                                         ║\n");
    printf("║             ╚═════╝ ╚══════╝                                         ║\n");
    printf("║                                                                      ║\n");
    printf("║   ██████╗██╗  ██╗ █████╗ ███╗   ██╗ ██████╗ ███████╗    ███╗   ███╗║\n");
    printf("║  ██╔════╝██║  ██║██╔══██╗████╗  ██║██╔════╝ ██╔════╝    ████╗ ████║║\n");
    printf("║  ██║     ███████║███████║██╔██╗ ██║██║  ███╗█████╗      ██╔████╔██║║\n");
    printf("║  ██║     ██╔══██║██╔══██║██║╚██╗██║██║   ██║██╔══╝      ██║╚██╔╝██║║\n");
    printf("║  ╚██████╗██║  ██║██║  ██║██║ ╚████║╚██████╔╝███████╗    ██║ ╚═╝ ██║║\n");
    printf("║   ╚═════╝╚═╝  ╚═╝╚═╝  ╚═╝╚═╝  ╚═══╝ ╚═════╝ ╚══════╝    ╚═╝     ╚═╝║\n");
    printf("║                                                                      ║\n");
    printf("║             ██╗███╗   ██╗██████╗                                    ║\n");
    printf("║             ██║████╗  ██║██╔══██╗                                   ║\n");
    printf("║             ██║██╔██╗ ██║██║  ██║                                   ║\n");
    printf("║             ██║██║╚██╗██║██║  ██║                                   ║\n");
    printf("║             ██║██║ ╚████║██████╔╝                                   ║\n");
    printf("║             ╚═╝╚═╝  ╚═══╝╚═════╝                                    ║\n");
    printf("╚══════════════════════════════════════════════════════════════════════╝\n");
    printf("\033[0m"); // Reset color
}

int main(int argc, char *argv[]) {
    // Default to list view
    const char* view_file = "apps/truth_challenge_game/truth_list_view.html";
    const char* view_type = "list";
    
    // Parse command line options
    static struct option long_options[] = {
        {"help", no_argument, 0, 'h'},
        {"game", no_argument, 0, 'g'},
        {"list", no_argument, 0, 'l'},
        {0, 0, 0, 0}
    };
    
    int opt;
    while ((opt = getopt_long(argc, argv, "hgl", long_options, NULL)) != -1) {
        switch (opt) {
            case 'h':
                print_usage(argv[0]);
                return 0;
            case 'g':
                view_file = "apps/truth_challenge_game/truth_challenge_enhanced.html";
                view_type = "game";
                break;
            case 'l':
                view_file = "apps/truth_challenge_game/truth_list_view.html";
                view_type = "list";
                break;
            default:
                print_usage(argv[0]);
                return 1;
        }
    }
    
    // Check if file exists
    if (access(view_file, R_OK) != 0) {
        // Try from different directory
        const char* fallback = (strcmp(view_type, "game") == 0) 
            ? "truth_challenge_enhanced.html" 
            : "truth_list_view.html";
        if (access(fallback, R_OK) != 0) {
            fprintf(stderr, "Error: Truth challenge %s file not found\n", view_type);
            fprintf(stderr, "Please run from the gate_computer project root directory\n");
            return 1;
        }
        view_file = fallback;
    }
    
    print_ascii_logo();
    
    printf("\n");
    printf("\033[33m"); // Yellow text
    if (strcmp(view_type, "game") == 0) {
        printf("                    CHALLENGE THE BASEFOLD RAA PROOF SYSTEM!\n");
        printf("\033[0m");
        printf("\n");
        printf("  Starting at Level 0: Mathematical Axioms (100%% confidence)\n");
        printf("  Your Goal: Reduce confidence below 50%% to win!\n");
        printf("\n");
        printf("  Each disputed truth reduces confidence by 5%%\n");
        printf("  Claude will defend each truth with mathematical arguments\n");
    } else {
        printf("                    TRUTH CHALLENGE CENTER - LIST VIEW\n");
        printf("\033[0m");
        printf("\n");
        printf("  Review all truth statements in an organized list\n");
        printf("  Search, filter, and manage your challenges\n");
        printf("\n");
        printf("  Use -g or --game flag to launch the interactive game view\n");
    }
    printf("\n");
    
    // Set up signal handler for cleanup
    signal(SIGINT, cleanup_server);
    signal(SIGTERM, cleanup_server);
    
    // Start a simple HTTP server
    server_pid = fork();
    if (server_pid == 0) {
        // Child process - run HTTP server silently
        freopen("/dev/null", "w", stdout);
        freopen("/dev/null", "w", stderr);
        execlp("python3", "python3", "-m", "http.server", "8081", NULL);
        // If python3 fails, try python
        execlp("python", "python", "-m", "SimpleHTTPServer", "8081", NULL);
        exit(1);
    } else if (server_pid > 0) {
        // Parent process - wait a bit then open browser
        usleep(500000); // Wait 0.5 seconds for server to start
        
        printf("\033[32m"); // Green text
        printf("  Opening %s view in browser at http://localhost:8081/%s\n", view_type, view_file);
        printf("\033[0m");
        printf("\n");
        printf("  Press Ctrl+C to stop the server.\n");
        printf("\n");
        
        // Build URL
        char url[512];
        snprintf(url, sizeof(url), "http://localhost:8081/%s", view_file);
        
        // Try to open in browser
        char command[1024];
        #ifdef __APPLE__
            snprintf(command, sizeof(command), "open %s", url);
            system(command);
        #else
            snprintf(command, sizeof(command), 
                    "xdg-open %s 2>/dev/null || "
                    "sensible-browser %s 2>/dev/null || "
                    "firefox %s 2>/dev/null || "
                    "chromium %s 2>/dev/null || "
                    "google-chrome %s 2>/dev/null",
                    url, url, url, url, url);
            system(command);
        #endif
        
        printf("\033[36m"); // Cyan text
        printf("═══════════════════════════════════════════════════════════════════════\n");
        if (strcmp(view_type, "game") == 0) {
            printf("  Game is running! Navigate through the truth dependency tree!\n");
        } else {
            printf("  Truth list is running! Review and manage all truth statements!\n");
        }
        printf("═══════════════════════════════════════════════════════════════════════\n");
        printf("\033[0m");
        
        // Wait for the server process
        int status;
        waitpid(server_pid, &status, 0);
    } else {
        fprintf(stderr, "Error: Failed to start game server\n");
        return 1;
    }
    
    return 0;
}