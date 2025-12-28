#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "truth_verifier::truth_verifier" for configuration "Release"
set_property(TARGET truth_verifier::truth_verifier APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(truth_verifier::truth_verifier PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libtruth_verifier.a"
  )

list(APPEND _cmake_import_check_targets truth_verifier::truth_verifier )
list(APPEND _cmake_import_check_files_for_truth_verifier::truth_verifier "${_IMPORT_PREFIX}/lib/libtruth_verifier.a" )

# Import target "truth_verifier::verify_truths" for configuration "Release"
set_property(TARGET truth_verifier::verify_truths APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(truth_verifier::verify_truths PROPERTIES
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/bin/verify_truths"
  )

list(APPEND _cmake_import_check_targets truth_verifier::verify_truths )
list(APPEND _cmake_import_check_files_for_truth_verifier::verify_truths "${_IMPORT_PREFIX}/bin/verify_truths" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
