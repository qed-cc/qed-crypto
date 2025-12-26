# Dependencies.cmake
# Helper module for finding and configuring dependencies

# Example: Find threads package
macro(find_required_threads)
    set(THREADS_PREFER_PTHREAD_FLAG ON)
    find_package(Threads REQUIRED)
endmacro()

# Example: Find math library
macro(find_required_math)
    find_library(MATH_LIBRARY m)
    if(NOT MATH_LIBRARY)
        message(FATAL_ERROR "Math library not found")
    endif()
endmacro()

# Example: Configure GoogleTest
macro(configure_gtest)
    include(FetchContent)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG release-1.12.1
    )
    # For Windows: Prevent overriding the parent project's compiler/linker settings
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)
endmacro()

