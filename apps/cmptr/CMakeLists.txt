cmake_minimum_required(VERSION 3.10)
project(cmptr_app C)

# =============================================================================
# Cmptr Application - BaseFold RAA Exclusive
# =============================================================================

# Enable AVX optimizations by default on x86_64
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64")
    set(USE_AVX2 ON)
    set(USE_AVX512 ON)
endif()
    
# Set the application name
set(APP_NAME cmptr)

# Main application executable with BaseFold RAA ONLY
add_executable(${APP_NAME} 
    src/main.c
    src/circuit_format.c
    src/sha3_final.c
    src/evaluator.c
)

# Include directories
target_include_directories(${APP_NAME} PRIVATE 
    ${CMAKE_CURRENT_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/circuit_evaluator/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/basefold_raa/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/basefold/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/gf128/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/sha3/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/common/include
)

# Compilation flags and definitions
target_compile_definitions(${APP_NAME} PRIVATE 
    STANDALONE_BUILD
    ENABLE_BASEFOLD_RAA_ONLY
    ENABLE_PCLMUL
)

# Pass through AVX definitions
if(USE_AVX2)
    target_compile_definitions(${APP_NAME} PRIVATE USE_AVX2)
endif()

if(USE_AVX512)
    target_compile_definitions(${APP_NAME} PRIVATE USE_AVX512)
endif()

# Architecture-specific optimizations
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64")
    target_compile_options(${APP_NAME} PRIVATE
        -maes -msse4.1 -mavx -mavx2 -mpclmul
        -mavx512f -mavx512dq -mavx512vl -mavx512bw -mvpclmulqdq
        -O3 -march=native -fopenmp
    )
endif()

# Link libraries - ONLY BaseFold RAA
target_link_libraries(${APP_NAME} 
    PRIVATE
        basefold_raa  # The ONLY proof system we use
        basefold      # Required by main.c
        gf128
        sha3
        common
        m
        gomp  # OpenMP
)

# Link-time optimization
set_property(TARGET ${APP_NAME} PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)

# Enable comprehensive compiler warnings
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
enable_cmptr_warnings(${APP_NAME})

# =============================================================================
# Utility Tools
# =============================================================================

# Gate counting tool
set(GATE_COUNT_TOOL count_gate_types)
add_executable(${GATE_COUNT_TOOL}
    tools/count_gate_types.c
    src/sha3_final.c
    src/circuit_format.c
    src/evaluator.c
)

target_include_directories(${GATE_COUNT_TOOL} PRIVATE 
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/circuit_evaluator/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/common/include
)

target_compile_definitions(${GATE_COUNT_TOOL} PRIVATE 
    STANDALONE_BUILD 
)

target_link_libraries(${GATE_COUNT_TOOL} PRIVATE common)

# Enable compiler warnings for tools
enable_cmptr_warnings(${GATE_COUNT_TOOL})

# Trace evaluation tool
set(TRACE_EVAL_TOOL trace_evaluation)
add_executable(${TRACE_EVAL_TOOL}
    tools/trace_evaluation.c
    src/sha3_final.c
    src/circuit_format.c
    src/evaluator.c
)

target_include_directories(${TRACE_EVAL_TOOL} PRIVATE 
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/circuit_evaluator/include
    ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/common/include
)

target_compile_definitions(${TRACE_EVAL_TOOL} PRIVATE 
    STANDALONE_BUILD 
)

target_link_libraries(${TRACE_EVAL_TOOL} PRIVATE common)

# Enable compiler warnings
enable_cmptr_warnings(${TRACE_EVAL_TOOL})

# =============================================================================
# Optional WebView Integration
# =============================================================================

# Check for WebView dependencies
find_package(PkgConfig)
if(PKG_CONFIG_FOUND)
    pkg_check_modules(GTK3 gtk+-3.0)
    pkg_check_modules(WEBKIT webkit2gtk-4.0)
    
    if(GTK3_FOUND AND WEBKIT_FOUND AND BUILD_WEBVIEW)
        message(STATUS "Building cmptr with WebView support")
        
        # WebView-enabled version
        add_executable(${APP_NAME}_webview
            src/main_webview.c
            src/circuit_format.c
            src/sha3_final.c
            src/evaluator.c
        )
        
        target_compile_definitions(${APP_NAME}_webview PRIVATE 
            USE_WEBVIEW=1
            STANDALONE_BUILD
            ENABLE_BASEFOLD_RAA_ONLY
            ENABLE_PCLMUL
        )
        
        target_include_directories(${APP_NAME}_webview PRIVATE 
            ${CMAKE_CURRENT_SOURCE_DIR}/src
            ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/circuit_evaluator/include
            ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/basefold_raa/include
            ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/basefold/include
            ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/gf128/include
            ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/sha3/include
            ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/common/include
            ${GTK3_INCLUDE_DIRS}
            ${WEBKIT_INCLUDE_DIRS}
        )
        
        target_link_libraries(${APP_NAME}_webview PRIVATE
            basefold_raa
            basefold
            gf128
            sha3
            common
            m
            gomp
            ${GTK3_LIBRARIES}
            ${WEBKIT_LIBRARIES}
        )
        
        # Enable compiler warnings
        enable_cmptr_warnings(${APP_NAME}_webview)
        
        # Install WebView version
        install(TARGETS ${APP_NAME}_webview DESTINATION bin)
    else()
        message(STATUS "WebView support disabled (missing GTK3/WebKit or BUILD_WEBVIEW not set)")
    endif()
endif()

# =============================================================================
# Installation
# =============================================================================

# Install the main executable and utilities
install(TARGETS 
    ${APP_NAME} 
    ${GATE_COUNT_TOOL}
    ${TRACE_EVAL_TOOL}
    DESTINATION bin
)