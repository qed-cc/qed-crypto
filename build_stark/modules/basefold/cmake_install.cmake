# Install script for directory: /home/bob/github/qedc-5/qed-crypto/modules/basefold

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "0")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set path to fallback-tool for dependency-resolution.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/home/bob/github/qedc-5/qed-crypto/build_stark/lib/libbasefold.a")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include" TYPE FILE FILES
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/basefold_trace.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/prg.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/transcript.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/enc.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/merkle/build.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/merkle/verify.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/gate_sumcheck.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/wiring.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/wiring_sumcheck.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/fold_reduce.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/polynomial_gf128.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/multilinear.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/vanishing_poly.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/gate_sumcheck_multilinear.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/gate_sumcheck_zk.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/merkle_commitment.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/evaluation_domain.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/extended_domain_utils.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/evaluation_path.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/merkle_sumcheck_binding.h"
    "/home/bob/github/qedc-5/qed-crypto/modules/basefold/include/binary_ntt.h"
    )
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/basefold" TYPE FILE FILES "/home/bob/github/qedc-5/qed-crypto/build_stark/modules/basefold/basefoldConfig.cmake")
endif()

string(REPLACE ";" "\n" CMAKE_INSTALL_MANIFEST_CONTENT
       "${CMAKE_INSTALL_MANIFEST_FILES}")
if(CMAKE_INSTALL_LOCAL_ONLY)
  file(WRITE "/home/bob/github/qedc-5/qed-crypto/build_stark/modules/basefold/install_local_manifest.txt"
     "${CMAKE_INSTALL_MANIFEST_CONTENT}")
endif()
