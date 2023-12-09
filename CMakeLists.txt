cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 11)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

file(READ "${CMAKE_CURRENT_SOURCE_DIR}/VERSION" CADICAL_VERSION)
# remove version suffix to make make it valid for cmake
string(REGEX REPLACE "([0-9]+\.[0-9]+\.[0-9]+).*$" "\\1" CADICAL_VERSION
                     "${CADICAL_VERSION}")

project(
  cadical
  LANGUAGES CXX
  VERSION ${CADICAL_VERSION})

file(
  GLOB_RECURSE SOURCES
  RELATIVE ${CMAKE_CURRENT_SOURCE_DIR}
  "src/*.cpp" "src/*.hpp")

list(REMOVE_ITEM SOURCES "src/mobical.cpp")
list(REMOVE_ITEM SOURCES "src/cadical.cpp")

add_library(cadical STATIC ${SOURCES})
add_library(cadical::cadical ALIAS cadical)
# don't generate the build header file when building the library
target_compile_definitions(cadical PRIVATE NBUILD=1)

target_include_directories(
  cadical INTERFACE $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
                    $<INSTALL_INTERFACE:include>)
