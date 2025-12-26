cmake_minimum_required(VERSION 3.10)
project(truth_verifier C)

# Add library
add_library(truth_verifier STATIC
    src/truth_verifier.c
    src/cmptr_truths.c
    src/performance_truths.c
    src/security_truths.c
    src/implementation_truths.c
    src/performance_falses.c
    src/future_uncertain.c
    src/optimization_truths.c
    src/optimization_false_buckets.c
    src/soundness_wip_truths.c
    src/proving_time_wip_truths.c
    src/recursive_optimization_truths.c
    src/recursive_advanced_truths.c
    src/zero_knowledge_axiom.c
    src/recursive_final_truths.c
    src/empirical_truths.c
    src/reality_check_truths.c
    src/achievement_truths.c
    src/security_proof_truths.c
    src/sub_second_optimization_truths.c
    src/optimized_security_truths.c
    src/circular_recursion_truths.c
    src/circular_recursion_wip_truths.c
    src/circular_recursion_achieved.c
    # src/proof_timing_truths.c  # Missing file
    src/truth_dependency_system.c
    src/circuit_security_axioms.c
    src/confidence_boost_wip_truths.c
    # src/proof_tracking.c  # Missing file
    src/expanded_truth_definitions.c
    src/atomic_truth_steps.c
    # src/expanded_clean_truths.c  # Has errors
    # src/mathematical_truth_atoms.c  # Has errors
    src/recursive_pos_truths.c
    src/pos_optimization_truths.c
    src/security_128bit_truths.c
    # src/comprehensive_proof_registry.c  # Missing dependency
    src/example_truths.c
    src/formal_integration_example.c
    # src/ultimate_mathematical_proofs.c  # Has errors
    src/detective_findings_truths.c
)

# Include directories
target_include_directories(truth_verifier
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
)

# Create executable
add_executable(verify_truths src/main.c)
target_link_libraries(verify_truths PRIVATE truth_verifier m)

# Create proof status reporter
# add_executable(proof_status_reporter ../../tools/proof_status_reporter.c)  # Missing file
# target_link_libraries(proof_status_reporter PRIVATE truth_verifier m)

# Installation rules
install(TARGETS truth_verifier verify_truths
    EXPORT truth_verifierTargets
    RUNTIME DESTINATION bin
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)

install(DIRECTORY include/
    DESTINATION include
)

# Export targets
install(EXPORT truth_verifierTargets
    FILE truth_verifierTargets.cmake
    NAMESPACE truth_verifier::
    DESTINATION lib/cmake/truth_verifier
)

# Create config file
configure_file(cmake/truth_verifierConfig.cmake.in
    "${CMAKE_CURRENT_BINARY_DIR}/truth_verifierConfig.cmake"
    @ONLY
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/truth_verifierConfig.cmake"
    DESTINATION lib/cmake/truth_verifier
)

# Add tests if testing is enabled
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()