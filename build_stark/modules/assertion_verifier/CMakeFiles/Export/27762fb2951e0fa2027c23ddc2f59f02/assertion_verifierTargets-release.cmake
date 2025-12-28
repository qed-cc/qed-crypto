#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "assertion_verifier::assertion_verifier" for configuration "Release"
set_property(TARGET assertion_verifier::assertion_verifier APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(assertion_verifier::assertion_verifier PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libassertion_verifier.a"
  )

list(APPEND _cmake_import_check_targets assertion_verifier::assertion_verifier )
list(APPEND _cmake_import_check_files_for_assertion_verifier::assertion_verifier "${_IMPORT_PREFIX}/lib/libassertion_verifier.a" )

# Import target "assertion_verifier::verify_assertions" for configuration "Release"
set_property(TARGET assertion_verifier::verify_assertions APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(assertion_verifier::verify_assertions PROPERTIES
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/bin/verify_assertions"
  )

list(APPEND _cmake_import_check_targets assertion_verifier::verify_assertions )
list(APPEND _cmake_import_check_files_for_assertion_verifier::verify_assertions "${_IMPORT_PREFIX}/bin/verify_assertions" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
