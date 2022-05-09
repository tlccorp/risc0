cmake_minimum_required(VERSION 3.10)
project(risc0)

set(CMAKE_VERBOSE_MAKEFILE ON)
set(CMAKE_CXX_STANDARD_REQUIRED True)


set (BUILD_HOST_VERIFY ON)
set (BUILD_RISCVM OFF)
set (BUILD_METHODS OFF)
set (BUILD_EOS ON)


if(BUILD_HOST_VERIFY)
	message("Building host verifier")
else()
	message (WARNING,"Builds for host verifier are disabled")
endif()

if(BUILD_RISCVM)
        message("Building risc VM")
else()
        message (WARNING,"Builds for risc VM are disabled")
endif()

if(BUILD_METHODS)
        message("Building methods")
else()
        message (WARNING,"Builds for methods are disabled")
endif()

if(BUILD_RISCVM)
	find_package(TBB REQUIRED)
endif()

if(BUILD_EOS)
	find_package(eosio.cdt REQUIRED)
	add_definitions(-DNO_CPP_STREAMS)
	add_definitions(-DNO_CPP_EXCEPTIONS)
endif()

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

include_directories(${risc0_SOURCE_DIR} ${CMAKE_BINARY_DIR}  )

add_subdirectory(risc0)
add_subdirectory(examples)
