cmake_minimum_required(VERSION 3.5)
project(gf128 VERSION 0.1.0 LANGUAGES C)
# Suppress INTERPROCEDURAL_OPTIMIZATION policy warnings
if(POLICY CMP0069)
  cmake_policy(SET CMP0069 NEW)
endif()
include(GNUInstallDirs)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
# Enable link-time optimization (LTO) for Release builds on GCC/Clang
if(CMAKE_BUILD_TYPE STREQUAL "Release" AND (CMAKE_C_COMPILER_ID STREQUAL "GNU" OR CMAKE_C_COMPILER_ID STREQUAL "Clang"))
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_RELEASE TRUE)
endif()

# Build options
option(ENABLE_TESTS "Build unit tests" OFF)
option(ENABLE_BENCHMARKS "Build benchmarks" ON)
option(ENABLE_EXAMPLES "Build examples" ON)
# Optimization options
option(USE_PCLMUL "Enable PCLMUL intrinsics implementation (requires PCLMUL, SSE4.1)" ON) # Default to ON as it's a core feature now
option(USE_PCLMUL_KARATSUBA "Enable Karatsuba PCLMUL intrinsics implementation (requires PCLMUL, SSE4.1)" OFF)
option(USE_AVX2 "Enable AVX2 intrinsics implementation (requires AVX2, PCLMUL)" OFF)
option(USE_AVX512 "Enable AVX-512 intrinsics implementation (requires AVX512F/DQ/BW/VL, PCLMUL)" OFF)
option(USE_GFNI   "Enable GFNI-accelerated reduction (requires AVX512GFNI, AVX512VBMI)" OFF)
option(USE_VNNI   "Enable VNNI-accelerated reduction (requires AVX512VNNI)" OFF)
option(USE_GFNI_MUL "Enable experimental pure GFNI multiply kernel" OFF)

# Architecture-specific microarchitecture tuning
option(ENABLE_MICROTUNE "Enable microarchitecture-specific tuning flags (-Ofast -march=native -flto)" OFF)
if(ENABLE_MICROTUNE)
    message(STATUS "Microtune: enabling -Ofast -march=native -flto for Release builds")
    # Append to Release compile flags
    set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -Ofast -march=native -flto")
    # Enable LTO for linker when applicable
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -flto")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -flto")
endif()

add_library(gf128
    src/gf128_base.c      # reference bitwise implementation (fallback)
    src/gf128_table.c     # table-driven fallback implementation
    src/gf128_inv.c
    src/gf128_dispatch.c  # generic multiply dispatch implementation
    src/cpu_features.c    # CPU feature detection implementation
)

# Include the PCLMUL intrinsic implementation for all PCLMUL-enabled builds
if(USE_PCLMUL)
    target_sources(gf128 PRIVATE src/gf128_pclmul.c)
    target_compile_definitions(gf128 PRIVATE HAVE_PCLMUL)
    message(STATUS "Including scalar PCLMUL intrinsic implementation.")
    # Compile PCLMUL intrinsic code with PCLMUL and SSE4.1 support
    set_source_files_properties(src/gf128_pclmul.c PROPERTIES
        COMPILE_FLAGS "-mpclmul -msse4.1"
    )
endif()

# Karatsuba PCLMUL variant (3 CLMULs)
if(USE_PCLMUL_KARATSUBA)
    target_sources(gf128 PRIVATE src/gf128_pclmul_kara.c)
    target_compile_definitions(gf128 PRIVATE USE_PCLMUL_KARATSUBA)
    message(STATUS "Including Karatsuba PCLMUL intrinsic implementation.")
    # Compile with PCLMUL and SSE4.1 support
    set_source_files_properties(src/gf128_pclmul_kara.c PROPERTIES
        COMPILE_FLAGS "-mpclmul -msse4.1"
    )
endif()

# Install-aware include directories: source dir when building, installed dir for consumers
target_include_directories(gf128
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
)

# Select only record-breaking multiply backends
# Select record-breaking multiply implementations; allow multiple backends
# AVX-512 4-way PCLMUL variant
if(USE_AVX512)
    target_sources(gf128 PRIVATE src/gf128_pclmul_avx512.c)
    target_compile_definitions(gf128 PRIVATE USE_AVX512)
    message(STATUS "Using AVX-512 4-way PCLMUL implementation.")
    # Compile AVX-512 PCLMUL code with AVX-512, CLMUL, and VBMI support
    # Compile with Ice Lake server microarchitecture to enable AVX-512, PCLMUL, GFNI, VBMI
    set_source_files_properties(src/gf128_pclmul_avx512.c PROPERTIES
        COMPILE_FLAGS "-march=icelake-server -mpclmul"
    )
endif()
if(USE_GFNI)
    target_compile_definitions(gf128 PRIVATE USE_GFNI)
    message(STATUS "Using GFNI-accelerated reduction.")
endif()
if(USE_GFNI_MUL)
    # Experimental pure-GFNI multiply implementation
    target_sources(gf128 PRIVATE src/gf128_gfni.c)
    target_compile_definitions(gf128 PRIVATE USE_GFNI_MUL USE_GFNI)
    # Compile with GFNI and VBMI support
    set_source_files_properties(src/gf128_gfni.c PROPERTIES
        COMPILE_FLAGS "-march=icelake-server -mpclmul -mavx512f -mavx512dq -mavx512bw -mavx512vl -mavx512vbmi"
    )
    message(STATUS "Including experimental GFNI-only multiply kernel (USE_GFNI_MUL enabled)")
endif()
if(USE_VNNI)
    target_compile_definitions(gf128 PRIVATE USE_VNNI)
    message(STATUS "Using VNNI-accelerated reduction.")
endif()

# AVX2 2-way PCLMUL variant
if(USE_AVX2)
    target_sources(gf128 PRIVATE src/gf128_pclmul_avx2.c)
    target_compile_definitions(gf128 PRIVATE USE_AVX2)
    message(STATUS "Using AVX2 2-way PCLMUL implementation.")
    # Compile AVX2 PCLMUL code with AVX2 and CLMUL support
    set_source_files_properties(src/gf128_pclmul_avx2.c PROPERTIES
        COMPILE_FLAGS "-mavx2 -mpclmul"
    )
endif()

if(NOT USE_AVX512 AND NOT USE_AVX2 AND NOT USE_PCLMUL)
    # Table-driven fallback (no PCLMUL support)
    message(STATUS "Using table-driven fallback implementation.")
endif()

# Expose ENABLE_PCLMUL macro for headers when PCLMUL is supported
include(CheckCCompilerFlag)
check_c_compiler_flag("-mpclmul" HAVE_C_PCLMUL)
if(HAVE_C_PCLMUL)
    target_compile_definitions(gf128 PUBLIC ENABLE_PCLMUL)
else()
    message(WARNING "Compiler does not support -mpclmul; PCLMUL path disabled")
endif()



if(ENABLE_TESTS)
  enable_testing()
  add_subdirectory(tests)
endif()
# Benchmarks and examples disabled in sandbox
# add_subdirectory(benchmarks)
# add_subdirectory(examples)

# Packaging and install targets
include(CMakePackageConfigHelpers)
# Install library and headers
install(TARGETS gf128 EXPORT gf128Targets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
    INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
install(DIRECTORY include/ DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
# Export targets for find_package
install(EXPORT gf128Targets
    FILE gf128Targets.cmake
    NAMESPACE gf128::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/gf128
)
# Generate and install CMake package configuration files
write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/gf128ConfigVersion.cmake"
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY AnyNewerVersion
)
configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/gf128Config.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/gf128Config.cmake"
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/gf128
)
install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/gf128Config.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/gf128ConfigVersion.cmake"
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/gf128
)
# Generate and install pkg-config file
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/pkgconfig/gf128.pc.in"
    "${CMAKE_CURRENT_BINARY_DIR}/gf128.pc"
    @ONLY
)
install(FILES "${CMAKE_CURRENT_BINARY_DIR}/gf128.pc"
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/pkgconfig
)