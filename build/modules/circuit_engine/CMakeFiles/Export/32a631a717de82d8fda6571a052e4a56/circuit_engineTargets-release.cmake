#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "circuit_engine::circuit_engine" for configuration "Release"
set_property(TARGET circuit_engine::circuit_engine APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(circuit_engine::circuit_engine PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libcircuit_engine.a"
  )

list(APPEND _cmake_import_check_targets circuit_engine::circuit_engine )
list(APPEND _cmake_import_check_files_for_circuit_engine::circuit_engine "${_IMPORT_PREFIX}/lib/libcircuit_engine.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
