# Tests CMakeLists.txt

# Include the CTest module for test discovery and reporting
include(CTest)

# Find a test framework (like CMocka)
# This is just an example, you might use a different testing framework
find_package(cmocka QUIET)

if(NOT cmocka_FOUND)
    # If CMocka is not found, we can use FetchContent to get it
    include(FetchContent)
    FetchContent_Declare(
        cmocka
        GIT_REPOSITORY https://git.cryptomilk.org/projects/cmocka.git
        GIT_TAG cmocka-1.1.5
    )
    FetchContent_MakeAvailable(cmocka)
    
    # Set the include directory
    set(CMOCKA_INCLUDE_DIR ${cmocka_SOURCE_DIR}/include)
endif()

# Function to add a test with standard configuration
function(add_gate_test TEST_NAME TEST_SOURCE)
    add_executable(${TEST_NAME} ${TEST_SOURCE} ${ARGN})
    
    target_include_directories(${TEST_NAME} PRIVATE ${CMOCKA_INCLUDE_DIR})
    
    # Link with cmocka and other dependencies
    target_link_libraries(${TEST_NAME}
        PRIVATE
            cmocka
            # Add other dependencies here as needed
    )
    
    # Add the test to CTest
    add_test(NAME ${TEST_NAME} COMMAND ${TEST_NAME})
endfunction()

# Add main test directories
add_subdirectory(unit)
add_subdirectory(integration)
add_subdirectory(security)
add_subdirectory(basefold_raa)
add_subdirectory(comprehensive)