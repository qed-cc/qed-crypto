#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "GateComputer::gate_core" for configuration "Release"
set_property(TARGET GateComputer::gate_core APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(GateComputer::gate_core PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libgate_core.a"
  )

list(APPEND _cmake_import_check_targets GateComputer::gate_core )
list(APPEND _cmake_import_check_files_for_GateComputer::gate_core "${_IMPORT_PREFIX}/lib/libgate_core.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
