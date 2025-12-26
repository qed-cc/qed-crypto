# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# CodeCoverage.cmake - Enable code coverage measurement for Gate Computer

# Function to setup coverage build type
function(setup_coverage_build)
    # Create Coverage build type
    set(CMAKE_CXX_FLAGS_COVERAGE
        "-g -O0 --coverage -fprofile-arcs -ftest-coverage"
        CACHE STRING "Flags used by the C++ compiler during coverage builds."
        FORCE)
    set(CMAKE_C_FLAGS_COVERAGE
        "-g -O0 --coverage -fprofile-arcs -ftest-coverage"
        CACHE STRING "Flags used by the C compiler during coverage builds."
        FORCE)
    set(CMAKE_EXE_LINKER_FLAGS_COVERAGE
        "--coverage -fprofile-arcs -ftest-coverage"
        CACHE STRING "Flags used for linking binaries during coverage builds."
        FORCE)
    set(CMAKE_SHARED_LINKER_FLAGS_COVERAGE
        "--coverage -fprofile-arcs -ftest-coverage"
        CACHE STRING "Flags used by the shared libraries linker during coverage builds."
        FORCE)
    
    # Update build types
    if(NOT CMAKE_BUILD_TYPE STREQUAL "Coverage")
        set(CMAKE_BUILD_TYPE_SHADOW ${CMAKE_BUILD_TYPE} CACHE STRING "Saved build type" FORCE)
    endif()
    
    set(CMAKE_BUILD_TYPE "Coverage" CACHE STRING "Build type" FORCE)
    
    # Mark for advanced users
    mark_as_advanced(
        CMAKE_CXX_FLAGS_COVERAGE
        CMAKE_C_FLAGS_COVERAGE
        CMAKE_EXE_LINKER_FLAGS_COVERAGE
        CMAKE_SHARED_LINKER_FLAGS_COVERAGE)
    
    message(STATUS "Code coverage build type enabled")
endfunction()

# Function to setup coverage target
function(setup_coverage_target)
    # Find required tools
    find_program(LCOV_PATH lcov)
    find_program(GENHTML_PATH genhtml)
    find_program(GCOV_PATH gcov)
    
    if(NOT LCOV_PATH)
        message(WARNING "lcov not found! Install lcov for coverage reports")
        return()
    endif()
    
    if(NOT GENHTML_PATH)
        message(WARNING "genhtml not found! Install lcov for HTML reports")
        return()
    endif()
    
    if(NOT GCOV_PATH)
        message(WARNING "gcov not found! Coverage will not work")
        return()
    endif()
    
    # Setup coverage output directory
    set(COVERAGE_OUTPUT_DIR ${CMAKE_BINARY_DIR}/coverage)
    file(MAKE_DIRECTORY ${COVERAGE_OUTPUT_DIR})
    
    # Add custom target for coverage collection
    add_custom_target(coverage
        COMMAND ${CMAKE_COMMAND} -E echo "Collecting coverage data..."
        
        # Clean previous coverage data
        COMMAND ${LCOV_PATH} --directory ${CMAKE_BINARY_DIR} --zerocounters
        COMMAND ${CMAKE_COMMAND} -E remove_directory ${COVERAGE_OUTPUT_DIR}
        COMMAND ${CMAKE_COMMAND} -E make_directory ${COVERAGE_OUTPUT_DIR}
        
        # Run tests
        COMMAND ${CMAKE_COMMAND} -E echo "Running tests..."
        COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
        
        # Capture coverage data
        COMMAND ${CMAKE_COMMAND} -E echo "Capturing coverage data..."
        COMMAND ${LCOV_PATH} --directory ${CMAKE_BINARY_DIR} --capture --output-file ${COVERAGE_OUTPUT_DIR}/coverage.info --gcov-tool ${GCOV_PATH}
        
        # Remove system headers and external libraries
        COMMAND ${LCOV_PATH} --remove ${COVERAGE_OUTPUT_DIR}/coverage.info 
            '/usr/*' 
            '*/vendor/*' 
            '*/build/*' 
            '*/tests/*' 
            '*/CMakeFiles/*'
            --output-file ${COVERAGE_OUTPUT_DIR}/coverage_cleaned.info
        
        # Generate HTML report
        COMMAND ${CMAKE_COMMAND} -E echo "Generating HTML report..."
        COMMAND ${GENHTML_PATH} ${COVERAGE_OUTPUT_DIR}/coverage_cleaned.info 
            --output-directory ${COVERAGE_OUTPUT_DIR}/html
            --demangle-cpp
            --num-spaces 4
            --sort
            --title "Gate Computer Code Coverage"
            --function-coverage
            --branch-coverage
            --legend
        
        # Summary
        COMMAND ${CMAKE_COMMAND} -E echo "Coverage report generated in ${COVERAGE_OUTPUT_DIR}/html/index.html"
        COMMAND ${LCOV_PATH} --summary ${COVERAGE_OUTPUT_DIR}/coverage_cleaned.info
        
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        COMMENT "Generating code coverage report..."
    )
    
    # Add target to reset coverage counters
    add_custom_target(coverage-reset
        COMMAND ${CMAKE_COMMAND} -E echo "Resetting coverage counters..."
        COMMAND ${LCOV_PATH} --directory ${CMAKE_BINARY_DIR} --zerocounters
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        COMMENT "Resetting code coverage counters..."
    )
    
    # Add target for quick coverage (no HTML generation)
    add_custom_target(coverage-quick
        COMMAND ${CMAKE_COMMAND} -E echo "Running quick coverage analysis..."
        COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
        COMMAND ${LCOV_PATH} --directory ${CMAKE_BINARY_DIR} --capture --output-file ${COVERAGE_OUTPUT_DIR}/coverage.info --gcov-tool ${GCOV_PATH}
        COMMAND ${LCOV_PATH} --summary ${COVERAGE_OUTPUT_DIR}/coverage.info
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        COMMENT "Running quick coverage analysis..."
    )
    
    # Add target to open coverage report
    add_custom_target(coverage-view
        COMMAND ${CMAKE_COMMAND} -E echo "Opening coverage report..."
        COMMAND xdg-open ${COVERAGE_OUTPUT_DIR}/html/index.html || open ${COVERAGE_OUTPUT_DIR}/html/index.html || start ${COVERAGE_OUTPUT_DIR}/html/index.html
        DEPENDS coverage
        COMMENT "Opening coverage report in browser..."
    )
endfunction()

# Function to add coverage to a specific target
function(target_enable_coverage target)
    if(CMAKE_BUILD_TYPE STREQUAL "Coverage")
        target_compile_options(${target} PRIVATE --coverage -fprofile-arcs -ftest-coverage)
        target_link_options(${target} PRIVATE --coverage -fprofile-arcs -ftest-coverage)
        
        # Add to global coverage targets list
        set_property(GLOBAL APPEND PROPERTY COVERAGE_TARGETS ${target})
    endif()
endfunction()

# Function to exclude target from coverage
function(target_exclude_coverage target)
    if(CMAKE_BUILD_TYPE STREQUAL "Coverage")
        set_target_properties(${target} PROPERTIES 
            COMPILE_FLAGS "-fno-profile-arcs -fno-test-coverage"
            LINK_FLAGS "-fno-profile-arcs -fno-test-coverage"
        )
    endif()
endfunction()

# Macro to setup coverage for the whole project
macro(enable_project_coverage)
    if(CMAKE_BUILD_TYPE STREQUAL "Coverage")
        message(STATUS "Code coverage measurement ENABLED")
        setup_coverage_build()
        setup_coverage_target()
    endif()
endmacro()