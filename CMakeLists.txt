cmake_minimum_required(VERSION 3.10)
project(arena LANGUAGES C)

if(CMAKE_C_COMPILER_ID MATCHES "GNU")
  add_compile_options(
    -Wall -Wextra -Wconversion -Wunused -Winfinite-recursion
    -Wmissing-prototypes -Wstrict-prototypes -Wshadow -Wformat=2
    -Wcast-align -Wmissing-declarations -Wstrict-overflow=5)
  if(CMAKE_GENERATOR STREQUAL "Ninja")
    add_compile_options(-fdiagnostics-color=always)
  endif()
elseif(CMAKE_C_COMPILER_ID MATCHES "Clang")
  add_compile_options(
    -Wall -Wextra -Wconversion -Wunused -Winfinite-recursion -Wassign-enum
    -Wcomma -Wdocumentation -Wmissing-prototypes -Wstrict-prototypes
    -Wconditional-uninitialized -Wshadow -Wformat=2 -Wcast-align
    -Wmissing-declarations -Wstrict-overflow=5)
  if(CMAKE_GENERATOR STREQUAL "Ninja")
    add_compile_options(-Xclang -fcolor-diagnostics)
  endif()
elseif(CMAKE_C_COMPILER_ID STREQUAL "MSVC")
  add_compile_options(/W3)
endif()

add_executable(test test.c arena.c)
