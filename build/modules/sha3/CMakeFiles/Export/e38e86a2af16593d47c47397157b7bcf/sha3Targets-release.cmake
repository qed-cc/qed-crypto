#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "sha3" for configuration "Release"
set_property(TARGET sha3 APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(sha3 PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libsha3.a"
  )

list(APPEND _cmake_import_check_targets sha3 )
list(APPEND _cmake_import_check_files_for_sha3 "${_IMPORT_PREFIX}/lib/libsha3.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
