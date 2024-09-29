cmake_minimum_required(VERSION 3.27)

project(CaDiCaL VERSION 2.0.0 LANGUAGES CXX)

add_compile_definitions(NBUILD)

add_library(libcadical
    src/analyze.cpp
    src/arena.cpp
    src/assume.cpp
    src/averages.cpp
    src/backtrack.cpp
    src/backward.cpp
    src/bins.cpp
    src/block.cpp
    src/ccadical.cpp
    src/checker.cpp
    src/clause.cpp
    src/collect.cpp
    src/compact.cpp
    src/condition.cpp
    src/config.cpp
    src/constrain.cpp
    src/contract.cpp
    src/cover.cpp
    src/decide.cpp
    src/decompose.cpp
    src/deduplicate.cpp
    src/drattracer.cpp
    src/elim.cpp
    src/ema.cpp
    src/extend.cpp
    src/external.cpp
    src/external_propagate.cpp
    src/file.cpp
    src/flags.cpp
    src/flip.cpp
    src/format.cpp
    src/frattracer.cpp
    src/gates.cpp
    src/idruptracer.cpp
    src/instantiate.cpp
    src/internal.cpp
    src/ipasir.cpp
    src/lidruptracer.cpp
    src/limit.cpp
    src/logging.cpp
    src/lookahead.cpp
    src/lratbuilder.cpp
    src/lratchecker.cpp
    src/lrattracer.cpp
    src/lucky.cpp
    src/message.cpp
    src/minimize.cpp
    src/occs.cpp
    src/options.cpp
    src/parse.cpp
    src/phases.cpp
    src/probe.cpp
    src/profile.cpp
    src/proof.cpp
    src/propagate.cpp
    src/queue.cpp
    src/random.cpp
    src/reap.cpp
    src/reduce.cpp
    src/rephase.cpp
    src/report.cpp
    src/resources.cpp
    src/restart.cpp
    src/restore.cpp
    src/score.cpp
    src/shrink.cpp
    src/signal.cpp
    src/solution.cpp
    src/solver.cpp
    src/stats.cpp
    src/subsume.cpp
    src/terminal.cpp
    src/ternary.cpp
    src/transred.cpp
    src/util.cpp
    src/var.cpp
    src/veripbtracer.cpp
    src/version.cpp
    src/vivify.cpp
    src/walk.cpp
    src/watch.cpp
)

set_target_properties(libcadical PROPERTIES
    OUTPUT_NAME "cadical"
    PUBLIC_HEADER src/cadical.hpp
)

add_library(cadicraig contrib/craigtracer.cpp)
target_include_directories(cadicraig PRIVATE src)
set_target_properties(cadicraig PROPERTIES PUBLIC_HEADER contrib/craigtracer.hpp)

add_executable(cadical src/cadical.cpp)
add_executable(mobical src/mobical.cpp)

target_link_libraries(cadical libcadical)
target_link_libraries(mobical libcadical)

install(TARGETS libcadical cadicraig cadical mobical)
