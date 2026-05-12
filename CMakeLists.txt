cmake_minimum_required(VERSION 3.17)

if (${APPLE})
    # if it's a macOS, target x86_64
    #set(CMAKE_OSX_ARCHITECTURES "x86_64")
endif ()
IF (APPLE)
    set(CMAKE_THREAD_LIBS_INIT "-lpthread")
    set(CMAKE_HAVE_THREADS_LIBRARY 1)
    set(CMAKE_USE_WIN32_THREADS_INIT 0)
    set(CMAKE_USE_PTHREADS_INIT 1)
    set(THREADS_PREFER_PTHREAD_FLAG ON)
ENDIF ()

project(tapis)

set(CMAKE_CXX_STANDARD 17)

if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif ()
string(APPEND CMAKE_CXX_FLAGS_RELEASE " -O3")
string(APPEND CMAKE_CC_FLAGS_RELEASE " -O3")

include_directories(include)

add_subdirectory(external/smtface)
include_directories(external/smtface/include)
include_directories(external/rope.hh/include)
include_directories(external/sexpresso/sexpresso)
include_directories(external/sexpresso/sexpresso_std)

add_subdirectory(src)

find_package(LLVM REQUIRED CONFIG)
message(${LLVM_INCLUDE_DIRS})
include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})
llvm_map_components_to_libnames(llvm_libs
        Core
        Support
        Option
        FrontendOpenMP
        FrontendHLSL
        WindowsDriver)

add_executable(tapis src/tapis/bin/tapis.cc external/sexpresso/sexpresso/sexpresso.cpp)
target_link_libraries(tapis
        tapislib
        hcvc
        smtface
        # apron
        apronxx
        apron
        boxD
        octD
        polkaMPQ
        mpfr
        gmp
        gmpxx
        # z3
        z3 pthread
        # clang
        clangSupport
        clangAPINotes
        clangASTMatchers
        clangFrontend
        clangSerialization
        clangDriver
        clangParse
        clangSema
        clangAnalysis
        clangAST
        clangBasic
        clangEdit
        clangLex
        clangTooling
        ${llvm_libs}
)
