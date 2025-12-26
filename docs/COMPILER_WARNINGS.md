/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# Compiler Warnings Configuration

## Overview

Gate Computer uses comprehensive compiler warnings to catch potential issues early in development. This document describes the warning flags enabled and how to use them in new modules.

## Warning Flags

### Basic Warnings
- `-Wall` - Enable most common warnings
- `-Wextra` - Enable additional warnings not covered by -Wall

### Type Safety Warnings
- `-Wconversion` - Warn about type conversions that may alter values
- `-Wsign-conversion` - Warn about sign conversions
- `-Wdouble-promotion` - Warn about float to double promotions
- `-Wcast-qual` - Warn about casts that remove qualifiers
- `-Wcast-align` - Warn about casts that increase alignment requirements

### Code Quality Warnings
- `-Wshadow` - Warn about variable shadowing
- `-Wunused` - Warn about unused entities
- `-Wundef` - Warn about undefined macros
- `-Wuninitialized` - Warn about uninitialized variables
- `-Winit-self` - Warn about self-initialization

### Function Declaration Warnings
- `-Wmissing-prototypes` - Warn about missing prototypes
- `-Wstrict-prototypes` - Warn about functions without prototypes
- `-Wold-style-definition` - Warn about old-style function definitions
- `-Wmissing-declarations` - Warn about missing declarations
- `-Wredundant-decls` - Warn about redundant declarations
- `-Wnested-externs` - Warn about nested extern declarations

### Security Warnings
- `-Wpointer-arith` - Warn about pointer arithmetic
- `-Wwrite-strings` - Warn about string literal modifications
- `-Wstrict-overflow=2` - Warn about overflow in comparisons
- `-Wformat -Wformat-security` - Format string security (enabled globally)

### GCC-Specific Warnings
When using GCC, these additional warnings are enabled:
- `-Wduplicated-cond` - Warn about duplicated conditions
- `-Wduplicated-branches` - Warn about duplicated branches
- `-Wrestrict` - Warn about restrict qualifier violations
- `-Wnull-dereference` - Warn about null pointer dereferences
- `-Wjump-misses-init` - Warn about jumps that miss variable initialization
- `-Wlogical-op` - Warn about suspicious logical operations

### Disabled Warnings
- `-Wno-unused-parameter` - Disabled as unused parameters are common in callback functions

## Usage in New Modules

### For Library Targets

```cmake
# In your module's CMakeLists.txt
add_library(my_module STATIC ${SOURCES})

# Enable comprehensive warnings
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
enable_gate_computer_warnings(my_module)
```

### For Executable Targets

```cmake
# In your app's CMakeLists.txt
add_executable(my_app ${SOURCES})

# Enable comprehensive warnings
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
enable_gate_computer_warnings(my_app)
```

### For Header-Only Libraries

```cmake
# For interface libraries
add_library(my_headers INTERFACE)

# Enable warnings for consumers
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
enable_gate_computer_warnings_interface(my_headers)
```

## Module Template

A complete CMakeLists.txt template with warnings pre-configured is available at:
`cmake/ModuleTemplate.cmake`

Copy this file to start a new module with all best practices already in place.

## Handling Warnings

### During Development

1. **Fix warnings immediately** - Don't let them accumulate
2. **Understand each warning** - Don't just silence them
3. **Use explicit casts** - When conversions are intentional
4. **Document suppressions** - If you must disable a warning, explain why

### Common Warning Fixes

#### Sign Conversion
```c
// Warning: implicit conversion changes signedness
size_t len = strlen(str);
int i = len;  // Warning!

// Fix: Use explicit cast if intentional
int i = (int)len;  // OK if you know len fits in int
```

#### Unused Parameter
```c
// Warning: unused parameter 'data'
void callback(int event, void *data) {
    handle_event(event);
}

// Fix: Use attribute or cast to void
void callback(int event, void *data) {
    (void)data;  // Explicitly unused
    handle_event(event);
}
```

#### Shadow Variables
```c
// Warning: declaration shadows a variable
int process(int count) {
    for (int count = 0; count < 10; count++) {  // Shadows parameter!
        // ...
    }
}

// Fix: Use different name
int process(int count) {
    for (int i = 0; i < 10; i++) {  // OK
        // ...
    }
}
```

## Future: -Werror

Once all warnings are fixed across the codebase, we plan to enable `-Werror` to treat all warnings as errors. This will enforce a zero-warning policy going forward.

## Platform Differences

Note that different compilers may produce different warnings:
- GCC tends to have more detailed warnings
- Clang's `-Weverything` is available but too noisy for production
- MSVC has its own warning system (not covered here as we use C99)

Always test with multiple compilers when possible.