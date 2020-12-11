# CMake functions to invoke modality-probe CLI subcommands.
#
# Example:
# ```cmake
# find_package(ModalityProbe REQUIRED)
#
# include(ModalityProbeCli)
#
# modality_probe_generate_manifest(
#     TARGET example
#     DEPENDS src/main.c
#     COMPONENT_NAME "example-component"
#     OUTPUT_PATH "example-component"
#     EXCLUDES "ignore-this/" "build/"
#     FILE_EXTENSIONS "c" "cpp"
#     SOURCE_PATH ".")
#
# modality_probe_generate_header(
#     TARGET example
#     OUTPUT_FILE "include/component_definitions.h"
#     COMPONENT_PATH "example-component")
#
# target_link_libraries(example PRIVATE ModalityProbe::LibModalityProbe)
# ```

# modality_probe_generate_manifest
#
# This function adds a custom command and target that invokes the modality-probe CLI
# manifest-gen subcommand. See `modality-probe manifest-gen --help` for more information.
#
# Usage:
# ```cmake
# modality_probe_generate_manifest(
#     TARGET <target>
#     OUTPUT_PATH <path>
#     SOURCE_PATH <path>
#     [REGEN_COMPONENT_ID <bool>]
#     [LANG <string>]
#     [DEPENDS <file-or-target>]
#     [COMPONENT_NAME <string>]
#     [FILE_EXTENSIONS <strings>]
#     [EXCLUDES <paths>]
#     [WORKING_DIRECTORY <path>]
# )
# ```
#
# If `WORKING_DIRECTORY` is not set, it defaults to `CMAKE_CURRENT_SOURCE_DIR`.
# If `LANG` is not set, it defaults to `C`.
function(modality_probe_generate_manifest)
    if(NOT MODALITY_PROBE_CLI OR NOT EXISTS "${MODALITY_PROBE_CLI}")
        message(FATAL_ERROR "MODALITY_PROBE_CLI is not set, the ModalityProbe package must be imported "
            "in your CMakeLists.txt before using modality_probe_generate_manifest()")
    endif()

    cmake_parse_arguments(
        CLI_ARGS
        "REGEN_COMPONENT_ID"
        "TARGET;WORKING_DIRECTORY;DEPENDS;LANG;COMPONENT_NAME;EVENT_ID_OFFSET;PROBE_ID_RANGE;OUTPUT_PATH;SOURCE_PATH"
        "EXCLUDES;FILE_EXTENSIONS"
        ${ARGN})

    if(NOT CLI_ARGS_TARGET)
        message(FATAL_ERROR "TARGET is required")
    endif()

    if(NOT CLI_ARGS_SOURCE_PATH)
        message(FATAL_ERROR "SOURCE_PATH is required")
    endif()

    if(NOT CLI_ARGS_OUTPUT_PATH)
        message(FATAL_ERROR "OUTPUT_PATH is required")
    endif()

    if(NOT CLI_ARGS_WORKING_DIRECTORY)
        set(CLI_ARGS_WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}")
    endif()

    if(NOT CLI_ARGS_LANG)
        set(CLI_ARGS_LANG "C")
    endif()

    set(CLI_ARGS "manifest-gen --lang=${CLI_ARGS_LANG}")

    if(CLI_ARGS_REGEN_COMPONENT_ID)
        set(CLI_ARGS "${CLI_ARGS} --regen-component-id")
    endif()

    if(CLI_ARGS_COMPONENT_NAME)
        set(CLI_ARGS "${CLI_ARGS} --component-name=${CLI_ARGS_COMPONENT_NAME}")
    endif()

    if(CLI_ARGS_EVENT_ID_OFFSET)
        set(CLI_ARGS "${CLI_ARGS} --event-id-offset=${CLI_ARGS_EVENT_ID_OFFSET}")
    endif()

    if(CLI_ARGS_PROBE_ID_RANGE)
        set(CLI_ARGS "${CLI_ARGS} --probe-id-range=${CLI_ARGS_PROBE_ID_RANGE}")
    endif()

    foreach(file_ext IN LISTS CLI_ARGS_FILE_EXTENSIONS)
        set(CLI_ARGS "${CLI_ARGS} --file-extension=${file_ext}")
    endforeach()

    foreach(exclude IN LISTS CLI_ARGS_EXCLUDES)
        set(CLI_ARGS "${CLI_ARGS} --exclude=${exclude}")
    endforeach()

    if(CLI_ARGS_OUTPUT_PATH)
        set(CLI_ARGS "${CLI_ARGS} --output-path=${CLI_ARGS_OUTPUT_PATH}")
    endif()

    set(CLI_ARGS "${CLI_ARGS} ${CLI_ARGS_SOURCE_PATH}")
    separate_arguments(CLI_ARGS)

    set(_MANIFEST_FILES
        "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_OUTPUT_PATH}/Component.toml"
        "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_OUTPUT_PATH}/events.csv"
        "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_OUTPUT_PATH}/probes.csv")

    add_custom_command(
        OUTPUT ${_MANIFEST_FILES}
        COMMAND ${MODALITY_PROBE_CLI} ${CLI_ARGS}
        DEPENDS ${CLI_ARGS_DEPENDS}
        VERBATIM
        WORKING_DIRECTORY "${CLI_ARGS_WORKING_DIRECTORY}")

    add_custom_target(
        ${CLI_ARGS_TARGET}_generated_modality_probe_manifest
        DEPENDS ${_MANIFEST_FILES})
    unset(_MANIFEST_FILES)

    add_dependencies(${CLI_ARGS_TARGET} ${CLI_ARGS_TARGET}_generated_modality_probe_manifest)
endfunction()

# modality_probe_generate_header
#
# This function adds a custom command and target that invokes the modality-probe CLI
# header-gen subcommand. See `modality-probe header-gen --help` for more information.
#
# Usage:
# ```cmake
# modality_probe_generate_header(
#     TARGET <target>
#     COMPONENT_PATH <path>
#     OUTPUT_FILE <path>
#     [LANG <string>]
#     [WORKING_DIRECTORY <path>]
# )
# ```
#
# If `WORKING_DIRECTORY` is not set, it defaults to `CMAKE_CURRENT_SOURCE_DIR`.
# If `LANG` is not set, it defaults to `C`.
function(modality_probe_generate_header)
    if(NOT MODALITY_PROBE_CLI OR NOT EXISTS "${MODALITY_PROBE_CLI}")
        message(FATAL_ERROR "MODALITY_PROBE_CLI is not set, the ModalityProbe package must be imported "
            "in your CMakeLists.txt before using modality_probe_generate_header()")
    endif()

    cmake_parse_arguments(
        CLI_ARGS
        ""
        "TARGET;WORKING_DIRECTORY;LANG;COMPONENT_PATH;OUTPUT_FILE"
        ""
        ${ARGN})

    if(NOT CLI_ARGS_TARGET)
        message(FATAL_ERROR "TARGET is required")
    endif()

    if(NOT CLI_ARGS_COMPONENT_PATH)
        message(FATAL_ERROR "COMPONENT_PATH is required")
    endif()

    if(NOT CLI_ARGS_OUTPUT_FILE)
        message(FATAL_ERROR "OUTPUT_FILE is required")
    endif()

    if(NOT CLI_ARGS_WORKING_DIRECTORY)
        set(CLI_ARGS_WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}")
    endif()

    if(NOT CLI_ARGS_LANG)
        set(CLI_ARGS_LANG "C")
    endif()

    set(CLI_ARGS "header-gen --lang=${CLI_ARGS_LANG}")
    set(CLI_ARGS "${CLI_ARGS} --output-path=${CLI_ARGS_OUTPUT_FILE}")
    set(CLI_ARGS "${CLI_ARGS} ${CLI_ARGS_COMPONENT_PATH}")
    separate_arguments(CLI_ARGS)

    set(_MANIFEST_FILES
         "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_COMPONENT_PATH}/Component.toml"
         "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_COMPONENT_PATH}/events.csv"
         "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_COMPONENT_PATH}/probes.csv")

    add_custom_command(
        OUTPUT "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_OUTPUT_FILE}"
        COMMAND ${MODALITY_PROBE_CLI} ${CLI_ARGS}
        DEPENDS ${_MANIFEST_FILES}
        VERBATIM
        WORKING_DIRECTORY "${CLI_ARGS_WORKING_DIRECTORY}")
    unset(_MANIFEST_FILES)

    add_custom_target(
        ${CLI_ARGS_TARGET}_generated_modality_probe_header
        DEPENDS "${CLI_ARGS_WORKING_DIRECTORY}/${CLI_ARGS_OUTPUT_FILE}")
    add_dependencies(${CLI_ARGS_TARGET} ${CLI_ARGS_TARGET}_generated_modality_probe_header)
endfunction()
