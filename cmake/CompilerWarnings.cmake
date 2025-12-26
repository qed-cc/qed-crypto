# CompilerWarnings.cmake - Common compiler warning settings for Cmptr
#
# This file provides a function to enable comprehensive compiler warnings
# for all modules in the Cmptr project.
#
# Usage in module CMakeLists.txt:
#   include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
#   enable_cmptr_warnings(target_name)

function(enable_cmptr_warnings target)
    if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
        # Basic warning flags
        target_compile_options(${target} PRIVATE -Wall -Wextra)
        
        # Additional useful warnings
        target_compile_options(${target} PRIVATE
            -Wshadow                # Warn about variable shadowing
            -Wunused                # Warn about unused entities
            -Wconversion            # Warn about type conversions that may alter value
            -Wsign-conversion       # Warn about sign conversions
            -Wdouble-promotion      # Warn about float to double promotion
            -Wcast-qual             # Warn about casts that remove qualifiers
            -Wcast-align            # Warn about casts that increase alignment
            -Wmissing-prototypes    # Warn about missing prototypes
            -Wstrict-prototypes     # Warn about function declarations without prototypes
            -Wold-style-definition  # Warn about old-style function definitions
            -Wmissing-declarations  # Warn about missing declarations
            -Wredundant-decls       # Warn about redundant declarations
            -Wnested-externs        # Warn about nested extern declarations
            -Winline                # Warn when inline functions cannot be inlined
            -Wundef                 # Warn about undefined macros
            -Wuninitialized         # Warn about uninitialized variables
            -Winit-self             # Warn about self-initialization
            -Wpointer-arith         # Warn about pointer arithmetic
            -Wwrite-strings         # Warn about string literal modifications
            -Wstrict-overflow=2     # Warn about overflow in comparisons
            -Wno-unused-parameter   # Don't warn about unused parameters (common in callbacks)
        )
        
        # GCC-specific warnings
        if(CMAKE_C_COMPILER_ID STREQUAL "GNU")
            target_compile_options(${target} PRIVATE
                -Wduplicated-cond       # Warn about duplicated conditions
                -Wduplicated-branches   # Warn about duplicated branches
                -Wrestrict              # Warn about restrict violations
                -Wnull-dereference      # Warn about null dereferences
                -Wjump-misses-init      # Warn about jumps that miss initialization
                -Wlogical-op            # Warn about suspicious logical operations
            )
        endif()
        
        # Note: We don't use -Weverything for Clang as it's too noisy for production code
        # Individual warnings can be enabled as needed for specific modules
    endif()
endfunction()

# Function to enable warnings for an interface target (headers only)
function(enable_cmptr_warnings_interface target)
    if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
        # For interface libraries, we can only set interface compile options
        target_compile_options(${target} INTERFACE
            -Wall -Wextra
            -Wshadow
            -Wunused
            -Wconversion
            -Wsign-conversion
            -Wcast-qual
            -Wcast-align
            -Wpointer-arith
            -Wwrite-strings
            -Wno-unused-parameter
        )
    endif()
endfunction()