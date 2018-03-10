
file(GLOB cadical_source_files "*.hpp" "*.cpp")
list(REMOVE_ITEM cadical_source_files "app.cpp")
list(REMOVE_ITEM cadical_source_files "main.cpp")

add_library(cadical_lib ${cadical_source_files})
add_executable(cadical app.cpp main.cpp)
target_link_libraries(cadical cadical_lib)
