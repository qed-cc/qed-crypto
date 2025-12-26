/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <getopt.h>
#include "logger.h"
#include "input_validation.h"

// WebView integration
#ifdef USE_WEBVIEW
#include <gtk/gtk.h>
#include <webkit2/webkit2.h>

static int gtk_initialized = 0;

int show_html_report(const char* html_file) {
    // Validate input file path
    if (validate_file_path(html_file, true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        LOG_ERROR("webview", "Invalid HTML file path: %s", html_file);
        return -1;
    }
    
    // Initialize GTK if needed
    if (!gtk_initialized) {
        if (!gtk_init_check(NULL, NULL)) {
            LOG_ERROR("webview", "Failed to initialize GTK");
            return -1;
        }
        gtk_initialized = 1;
    }
    
    // Get absolute path
    char abs_path[4096];
    if (realpath(html_file, abs_path) == NULL) {
        LOG_ERROR("webview", "Cannot find file '%s'", html_file);
        return -1;
    }
    
    // Create window
    GtkWidget* window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title(GTK_WINDOW(window), "Gate Computer - Report Viewer");
    gtk_window_set_default_size(GTK_WINDOW(window), 1200, 800);
    gtk_window_set_position(GTK_WINDOW(window), GTK_WIN_POS_CENTER);
    
    // Create WebView
    WebKitWebView* webview = WEBKIT_WEB_VIEW(webkit_web_view_new());
    
    // Load the HTML file
    char url[4196];
    snprintf(url, sizeof(url), "file://%s", abs_path);
    webkit_web_view_load_uri(webview, url);
    
    // Add to window
    gtk_container_add(GTK_CONTAINER(window), GTK_WIDGET(webview));
    
    // Connect destroy signal
    g_signal_connect(window, "destroy", G_CALLBACK(gtk_main_quit), NULL);
    
    // Show everything
    gtk_widget_show_all(window);
    
    printf("Viewing: %s\n", abs_path);
    
    // Run GTK main loop
    gtk_main();
    
    return 0;
}
#endif

// Standard gate_computer functions
void print_usage(const char* program_name) {
    printf("Gate Computer - ZK Proof System with Integrated WebView\n");
    printf("Usage: %s [options]\n", program_name);
    printf("\nOptions:\n");
    printf("  --help                Show this help message\n");
    printf("  --gen-sha3-256        Generate SHA3-256 circuit\n");
    printf("  --input-text TEXT     Input text for hashing\n");
    printf("  --input-hex HEX       Input hex for hashing\n");
    printf("  --prove FILE          Generate proof and save to FILE\n");
    printf("  --verify FILE         Verify proof from FILE\n");
    printf("  --verbose             Enable verbose output\n");
    printf("\nWebView Options:\n");
    printf("  --view-report [FILE]  View HTML report (default: empirical_evidence/report/easy_read_report.html)\n");
    printf("  --view-html FILE      View any HTML file in integrated WebView\n");
    printf("\nExamples:\n");
    printf("  %s --view-report\n", program_name);
    printf("  %s --gen-sha3-256 --input-text \"test\" --prove proof.raa\n", program_name);
}

int main(int argc, char* argv[]) {
    // Command line options
    static struct option long_options[] = {
        {"help", no_argument, 0, 'h'},
        {"view-report", optional_argument, 0, 'r'},
        {"view-html", required_argument, 0, 'v'},
        {"gen-sha3-256", no_argument, 0, 's'},
        {"input-text", required_argument, 0, 't'},
        {"input-hex", required_argument, 0, 'x'},
        {"prove", required_argument, 0, 'p'},
        {"verify", required_argument, 0, 'V'},
        {"verbose", no_argument, 0, 'b'},
        {0, 0, 0, 0}
    };
    
    // Check for --view-report as first argument for quick access
    if (argc >= 2 && strcmp(argv[1], "--view-report") == 0) {
        #ifdef USE_WEBVIEW
            const char* file = "empirical_evidence/report/easy_read_report.html";
            if (argc >= 3 && argv[2][0] != '-') {
                file = argv[2];
            }
            return show_html_report(file);
        #else
            LOG_ERROR("webview", "WebView support not compiled in");
            LOG_ERROR("webview", "Rebuild with: make clean && make USE_WEBVIEW=1");
            return 1;
        #endif
    }
    
    // Parse all options
    int option_index = 0;
    int c;
    
    while ((c = getopt_long(argc, argv, "hr:v:st:x:p:V:b", long_options, &option_index)) != -1) {
        switch (c) {
            case 'h':
                print_usage(argv[0]);
                return 0;
                
            case 'r': // --view-report
                #ifdef USE_WEBVIEW
                {
                    const char* file = optarg ? optarg : "empirical_evidence/report/easy_read_report.html";
                    return show_html_report(file);
                }
                #else
                    LOG_ERROR("webview", "WebView support not compiled in");
                    LOG_ERROR("webview", "Rebuild with: make clean && make USE_WEBVIEW=1");
                    return 1;
                #endif
                
            case 'v': // --view-html
                #ifdef USE_WEBVIEW
                    return show_html_report(optarg);
                #else
                    LOG_ERROR("webview", "WebView support not compiled in");
                    LOG_ERROR("webview", "Rebuild with: make clean && make USE_WEBVIEW=1");
                    return 1;
                #endif
                
            // TODO: Handle other gate_computer options
            case 's':
            case 't':
            case 'x':
            case 'p':
            case 'V':
            case 'b':
                printf("Gate computer proof functionality not yet integrated\n");
                printf("Use --view-report to view HTML reports\n");
                return 1;
                
            default:
                print_usage(argv[0]);
                return 1;
        }
    }
    
    // No options provided
    print_usage(argv[0]);
    return 0;
}