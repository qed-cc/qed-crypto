#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "gf128::gf128" for configuration "Release"
set_property(TARGET gf128::gf128 APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(gf128::gf128 PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "C"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libgf128.a"
  )

list(APPEND _cmake_import_check_targets gf128::gf128 )
list(APPEND _cmake_import_check_files_for_gf128::gf128 "${_IMPORT_PREFIX}/lib/libgf128.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
