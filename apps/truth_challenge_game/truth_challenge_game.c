/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <gtk/gtk.h>
#include <webkit2/webkit2.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void destroy_window_cb(GtkWidget* widget, GtkWidget* window) {
    gtk_main_quit();
}

static gboolean close_webview_cb(WebKitWebView* webview, GtkWidget* window) {
    gtk_widget_destroy(window);
    return TRUE;
}

// JavaScript injection to enhance the game
static void inject_game_enhancements(WebKitWebView *web_view) {
    const char *script = 
        "console.log('Truth Challenge Game Enhanced!');"
        "document.body.style.userSelect = 'none';"
        "// Add keyboard shortcuts"
        "document.addEventListener('keydown', (e) => {"
        "  if (e.key === 'Escape') window.close();"
        "});";
    
    webkit_web_view_run_javascript(web_view, script, NULL, NULL, NULL);
}

static void load_changed_cb(WebKitWebView *web_view, WebKitLoadEvent load_event, gpointer user_data) {
    if (load_event == WEBKIT_LOAD_FINISHED) {
        inject_game_enhancements(web_view);
    }
}

int main(int argc, char *argv[]) {
    gtk_init(&argc, &argv);
    
    // Create main window
    GtkWidget *window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title(GTK_WINDOW(window), "This is TRUE - CHANGE MY MIND");
    gtk_window_set_default_size(GTK_WINDOW(window), 1400, 900);
    gtk_window_set_position(GTK_WINDOW(window), GTK_WIN_POS_CENTER);
    
    // Add window icon if available
    gtk_window_set_icon_name(GTK_WINDOW(window), "applications-games");
    
    // Create WebView
    WebKitWebView *web_view = WEBKIT_WEB_VIEW(webkit_web_view_new());
    
    // Configure WebView settings
    WebKitSettings *settings = webkit_web_view_get_settings(web_view);
    webkit_settings_set_enable_developer_extras(settings, TRUE);
    webkit_settings_set_enable_javascript(settings, TRUE);
    webkit_settings_set_javascript_can_open_windows_automatically(settings, FALSE);
    
    // Set up WebView context for better security
    WebKitWebContext *context = webkit_web_view_get_context(web_view);
    webkit_web_context_set_cache_model(context, WEBKIT_CACHE_MODEL_DOCUMENT_VIEWER);
    
    // Connect signals
    g_signal_connect(window, "destroy", G_CALLBACK(destroy_window_cb), NULL);
    g_signal_connect(web_view, "close", G_CALLBACK(close_webview_cb), window);
    g_signal_connect(web_view, "load-changed", G_CALLBACK(load_changed_cb), NULL);
    
    // Create scrolled window
    GtkWidget *scrolled_window = gtk_scrolled_window_new(NULL, NULL);
    gtk_container_add(GTK_CONTAINER(scrolled_window), GTK_WIDGET(web_view));
    gtk_container_add(GTK_CONTAINER(window), scrolled_window);
    
    // Load the HTML content directly (embedded)
    const char *html_content = 
#include "truth_game_embedded.h"
    ;
    
    webkit_web_view_load_html(web_view, html_content, "file:///");
    
    // Show everything
    gtk_widget_show_all(window);
    
    // Start GTK main loop
    gtk_main();
    
    return 0;
}