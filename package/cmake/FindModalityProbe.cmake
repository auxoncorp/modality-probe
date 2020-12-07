# CMake find script to locate modality-probe includes and library.
#
# This module defines the `ModalityProbe::LibModalityProbe` target when found.
#
# This module defines the following variables:
# * `ModalityProbe_FOUND` - True if modality-probe is found
# * `MODALITY_PROBE_INCLUDE_DIRS` - Include directories, where to find modality/probe.h, etc
# * `MODALITY_PROBE_LIBRARIES` - List of libraries to link when using modality-probe
# * `MODALITY_PROBE_LIBRARY_DIRS` - Library directories
# * `MODALITY_PROBE_BINARY_DIRS` - Binary directories
# * `MODALITY_PROBE_CLI` - Absolute path to modality-probe CLI
# * `MODALITY_PROBE_MAJOR_VERSION` - The major version number
# * `MODALITY_PROBE_MINOR_VERSION` - The minor version number
# * `MODALITY_PROBE_PATCH_VERSION` - The patch version number
#
# Users may set `MODALITY_PROBE_ROOT` to a modality-probe installation root directory
# to instruct this module where to look.
# Alternatively users can add this cmake directory path to `CMAKE_MODULE_PATH`, for example with:
# `list(APPEND CMAKE_MODULE_PATH "/path/to/modality-probe/cmake")`
#
# Users can change the default target triple `x86_64-unknown-linux-gnu`
# by setting the `MODALITY_PROBE_TARGET_TRIPLE` variable.
#
# Example:
# ```cmake
# find_package(ModalityProbe REQUIRED)
# target_link_libraries(your_target PRIVATE ModalityProbe::LibModalityProbe)
# ```

if(NOT MODALITY_PROBE_ROOT)
    get_filename_component(_PARENT_DIR "${CMAKE_CURRENT_LIST_DIR}" DIRECTORY)
    set(MODALITY_PROBE_ROOT "${_PARENT_DIR}" CACHE PATH "Installation directory")
    unset(_PARENT_DIR)
endif()

if(NOT MODALITY_PROBE_TARGET_TRIPLE)
    set(MODALITY_PROBE_TARGET_TRIPLE "x86_64-unknown-linux-gnu" CACHE STRING "Target triple")
endif()

set(MODALITY_PROBE_CMAKE_DIR "${MODALITY_PROBE_ROOT}/cmake")
set(MODALITY_PROBE_LIBRARY_DIR "${MODALITY_PROBE_ROOT}/lib/${MODALITY_PROBE_TARGET_TRIPLE}")
set(MODALITY_PROBE_BINARY_DIR "${MODALITY_PROBE_ROOT}/bin")

find_file(MODALITY_PROBE_VERSION_FILE
    VERSION
    PATHS "${MODALITY_PROBE_ROOT}"
    REQUIRED
    NO_DEFAULT_PATH)

find_path(MODALITY_PROBE_INCLUDE_DIR
    NAMES modality/probe.h
    PATHS "${MODALITY_PROBE_ROOT}"
    PATH_SUFFIXES include
    REQUIRED
    NO_DEFAULT_PATH)

find_library(MODALITY_PROBE_LIBRARY
    modality_probe
    PATH "${MODALITY_PROBE_LIBRARY_DIR}"
    REQUIRED
    NO_DEFAULT_PATH)

if(WIN32)
    set(_PROBE_CLI "modality-probe.exe")
else()
    set(_PROBE_CLI "modality-probe")
endif()
find_program(MODALITY_PROBE_CLI
    "${_PROBE_CLI}"
    PATHS "${MODALITY_PROBE_BINARY_DIR}"
    REQUIRED
    NO_DEFAULT_PATH)
unset(_PROBE_CLI)

mark_as_advanced(MODALITY_PROBE_INCLUDE_DIR MODALITY_PROBE_LIBRARY_DIR MODALITY_PROBE_BINARY_DIR)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(ModalityProbe DEFAULT_MSG
    MODALITY_PROBE_VERSION_FILE MODALITY_PROBE_INCLUDE_DIR MODALITY_PROBE_LIBRARY MODALITY_PROBE_CLI)

if(EXISTS "${MODALITY_PROBE_VERSION_FILE}")
    file(READ "${MODALITY_PROBE_VERSION_FILE}" MODALITY_PROBE_VERSION)
    string(REPLACE "." ";" VERSION_LIST ${MODALITY_PROBE_VERSION})
    list(GET VERSION_LIST 0 MODALITY_PROBE_VERSION_MAJOR)
    list(GET VERSION_LIST 1 MODALITY_PROBE_VERSION_MINOR)
    list(GET VERSION_LIST 2 MODALITY_PROBE_VERSION_PATCH)
    set(MODALITY_PROBE_MAJOR_VERSION "${MODALITY_PROBE_VERSION_MAJOR}")
    set(MODALITY_PROBE_MINOR_VERSION "${MODALITY_PROBE_VERSION_MINOR}")
    set(MODALITY_PROBE_PATCH_VERSION "${MODALITY_PROBE_VERSION_PATCH}")
endif()

if(ModalityProbe_FOUND)
    set(MODALITY_PROBE_INCLUDE_DIRS "${MODALITY_PROBE_INCLUDE_DIR}")
    set(MODALITY_PROBE_LIBRARY_DIRS "${MODALITY_PROBE_LIBRARY_DIR}")
    set(MODALITY_PROBE_LIBRARIES "${MODALITY_PROBE_LIBRARY}")
    set(MODALITY_PROBE_BINARY_DIRS "${MODALITY_PROBE_BINARY_DIR}")

    if(NOT TARGET ModalityProbe::LibModalityProbe)
        add_library(ModalityProbe::LibModalityProbe UNKNOWN IMPORTED)
        set_target_properties(ModalityProbe::LibModalityProbe PROPERTIES
            INTERFACE_INCLUDE_DIRECTORIES "${MODALITY_PROBE_INCLUDE_DIRS}")
        set_target_properties(ModalityProbe::LibModalityProbe PROPERTIES
            INTERFACE_INCLUDE_DIRECTORIES "${MODALITY_PROBE_INCLUDE_DIRS}"
            IMPORTED_LOCATION "${MODALITY_PROBE_LIBRARY}")
    endif()
endif()
