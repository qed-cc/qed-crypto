/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <stdbool.h>

/**
 * @file module_dependency_detective.c
 * @brief Analyzes module dependencies to find correct build order
 */

typedef struct {
    char name[256];
    char dependencies[10][256];
    int dep_count;
    bool has_cmake;
    bool visited;
} module_info_t;

/* Check if module has CMakeLists.txt */
static bool check_cmake_exists(const char *module_path) {
    char cmake_path[512];
    snprintf(cmake_path, sizeof(cmake_path), "%s/CMakeLists.txt", module_path);
    
    FILE *fp = fopen(cmake_path, "r");
    if (fp) {
        fclose(fp);
        return true;
    }
    return false;
}

/* Find dependencies in CMakeLists.txt */
static void find_dependencies(const char *module_path, module_info_t *module) {
    char cmake_path[512];
    snprintf(cmake_path, sizeof(cmake_path), "%s/CMakeLists.txt", module_path);
    
    FILE *fp = fopen(cmake_path, "r");
    if (!fp) return;
    
    char line[1024];
    module->dep_count = 0;
    
    while (fgets(line, sizeof(line), fp)) {
        // Look for find_package or target_link_libraries
        if (strstr(line, "find_package(") || strstr(line, "target_link_libraries(")) {
            // Common dependencies
            if (strstr(line, "circuit_evaluator")) {
                strcpy(module->dependencies[module->dep_count++], "circuit_evaluator");
            }
            if (strstr(line, "circuit_io")) {
                strcpy(module->dependencies[module->dep_count++], "circuit_io");
            }
            if (strstr(line, "circuit_encoder")) {
                strcpy(module->dependencies[module->dep_count++], "circuit_encoder");
            }
            if (strstr(line, "gf128")) {
                strcpy(module->dependencies[module->dep_count++], "gf128");
            }
            if (strstr(line, "sha3")) {
                strcpy(module->dependencies[module->dep_count++], "sha3");
            }
            if (strstr(line, "basefold")) {
                strcpy(module->dependencies[module->dep_count++], "basefold");
            }
        }
    }
    
    fclose(fp);
}

/* Main analysis */
int main() {
    printf("=== MODULE DEPENDENCY DETECTIVE ===\n\n");
    
    module_info_t modules[50];
    int module_count = 0;
    
    // Scan modules directory
    DIR *dir = opendir("modules");
    if (!dir) {
        printf("Cannot open modules directory\n");
        return 1;
    }
    
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        if (entry->d_name[0] == '.') continue;
        
        char module_path[512];
        snprintf(module_path, sizeof(module_path), "modules/%s", entry->d_name);
        
        // Check if it's a directory
        DIR *subdir = opendir(module_path);
        if (!subdir) continue;
        closedir(subdir);
        
        // Add to module list
        module_info_t *mod = &modules[module_count++];
        strcpy(mod->name, entry->d_name);
        mod->has_cmake = check_cmake_exists(module_path);
        mod->visited = false;
        
        if (mod->has_cmake) {
            find_dependencies(module_path, mod);
        }
    }
    closedir(dir);
    
    // Print module analysis
    printf("MODULES FOUND:\n");
    for (int i = 0; i < module_count; i++) {
        module_info_t *mod = &modules[i];
        printf("\n%s:\n", mod->name);
        printf("  Has CMakeLists.txt: %s\n", mod->has_cmake ? "YES" : "NO");
        
        if (mod->dep_count > 0) {
            printf("  Dependencies:\n");
            for (int j = 0; j < mod->dep_count; j++) {
                printf("    - %s\n", mod->dependencies[j]);
            }
        }
    }
    
    // Find circular dependencies
    printf("\n\nDEPENDENCY ANALYSIS:\n");
    
    // Check circuit modules specifically
    printf("\nCircuit module dependencies:\n");
    for (int i = 0; i < module_count; i++) {
        if (strstr(modules[i].name, "circuit")) {
            printf("  %s depends on:", modules[i].name);
            for (int j = 0; j < modules[i].dep_count; j++) {
                printf(" %s", modules[i].dependencies[j]);
            }
            printf("\n");
        }
    }
    
    printf("\n\nRECOMMENDED BUILD ORDER:\n");
    printf("1. common (no deps)\n");
    printf("2. sha3 (no deps)\n");
    printf("3. gf128 (no deps)\n");
    printf("4. circuit_evaluator (basic deps)\n");
    printf("5. circuit_encoder (may depend on evaluator)\n");
    printf("6. circuit_io (depends on evaluator)\n");
    printf("7. circuit_generator (depends on evaluator)\n");
    printf("8. basefold (depends on gf128, sha3)\n");
    printf("9. basefold_raa (depends on basefold, circuit_generator)\n");
    
    return 0;
}