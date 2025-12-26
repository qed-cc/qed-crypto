cmake_minimum_required(VERSION 3.14)

# Set C99 standard
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Project name and version
project(cmptr 
        VERSION 0.1.0
        DESCRIPTION "Cmptr - Digital Logic Simulator"
        LANGUAGES C)
## Redirect all temporary files into a writable subdirectory of the build tree
set(ENV{TMPDIR} "${CMAKE_BINARY_DIR}/tmp")
file(MAKE_DIRECTORY "${CMAKE_BINARY_DIR}/tmp")
 # Use pipes for compilation and linking to avoid /tmp usage
if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
  # Use '-pipe' to avoid temp files during compilation, applied to C compile only
  add_compile_options($<$<COMPILE_LANGUAGE:C>:-pipe>)
  # Do not use '-pipe' during linking to avoid temporary file errors on restricted /tmp
  # set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pipe")
endif()

# Add aggressive optimization flags for Release mode
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -O3 -march=native -mtune=native -funroll-loops -finline-functions -finline-limit=10000 -fomit-frame-pointer")
endif()

# Options
option(BUILD_TESTS "Build test programs" OFF)
option(BUILD_BENCHMARKS "Build benchmark programs" OFF)
option(BUILD_DOCS "Build documentation" OFF)
option(BUILD_GROTH16 "Build Groth16 zk-SNARK module (pre-quantum)" OFF)
option(BUILD_BASEFOLD_RAA "Build BaseFold RAA proof system (post-quantum)" ON)

# Security: Enable security hardening flags
if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
    # Stack protection
    add_compile_options(-fstack-protector-strong)
    
    # Fortify source
    add_compile_definitions(_FORTIFY_SOURCE=2)
    
    # Format string security
    add_compile_options(-Wformat -Wformat-security -Werror=format-security)
    
    # Position independent code
    set(CMAKE_POSITION_INDEPENDENT_CODE ON)
    
    # Full RELRO and immediate binding
    add_link_options(-Wl,-z,relro,-z,now)
    
    # NX bit (no-execute)
    add_link_options(-Wl,-z,noexecstack)
endif()

# Custom CMake modules path
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

# Output directories
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# Dependencies
include(FetchContent)
include(Dependencies)

# Find required system libraries
find_required_threads()
find_required_math()


# Find OpenMP for parallelization
find_package(OpenMP)
if(OpenMP_C_FOUND)
    message(STATUS "OpenMP found: ${OpenMP_C_VERSION}")
    # Add OpenMP flags to C compiler
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${OpenMP_EXE_LINKER_FLAGS}")
else()
    message(STATUS "OpenMP not found, building without parallelization")
endif()

# Include directories
include_directories(
    ${CMAKE_CURRENT_SOURCE_DIR}/include
)
# Use pipes to avoid GCC writing temp files to /tmp
if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
  # Use '-pipe' for C compilation only
  add_compile_options($<$<COMPILE_LANGUAGE:C>:-pipe>)
endif()

# Add modules (submodules will be included from here)
add_subdirectory(modules)

# Add source directory
add_subdirectory(src)

# Add applications
add_subdirectory(apps)

# Add examples
add_subdirectory(examples)


# Conditionally add tests
if(BUILD_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()

# Conditionally add benchmarks
if(BUILD_BENCHMARKS)
    add_subdirectory(benchmarks)
endif()

# Conditionally build documentation
if(BUILD_DOCS)
    add_subdirectory(docs)
endif()


# Install rules
install(DIRECTORY include/ DESTINATION include)