// vim: set tw=300: set VIM text width to 300 characters for this file.

#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Stats::Stats () {
  time.real = absolute_real_time ();
  time.process = absolute_process_time ();
  walk_minimum = INT64_MAX;
  used[0].resize (127);
  used[1].resize (127);
}

/*------------------------------------------------------------------------*/

#define PRT(FMT, ...) \
  do { \
    if (FMT[0] == ' ' && !all) \
      break; \
    MSG (FMT, __VA_ARGS__); \
  } while (0)

/*------------------------------------------------------------------------*/

#ifndef QUIET
void Stats::print_old (Internal *internal) {
  Stats &stats = internal->stats;
  double t = internal->solve_time ();
  int all = internal->opts.verbose > 0 || internal->opts.stats;
#ifdef LOGGING
  if (internal->opts.log)
    all = true;
#endif // ifdef LOGGING

  int64_t propagations = stats.propagations;

  int64_t vivified =
      stats.vivify_subsumed + stats.vivify_strength + stats.vivify_implied;
  int64_t searchticks =
      stats.ticks_search_stable + stats.ticks_search_unstable;
  int64_t inprobeticks = stats.ticks_vivify + stats.ticks_probe +
                         stats.ticks_factor + stats.ticks_ternary +
                         stats.ticks_sweep + stats.ticks_backbone;
  int64_t local_search_ticks = stats.ticks_walk;
  int64_t totalticks = searchticks + inprobeticks + local_search_ticks;
  assert (totalticks == stats.ticks);

  size_t extendbytes = internal->external->extension.size ();
  extendbytes *= sizeof (int);

  if (all || stats.backbone_rounds) {
    PRT ("backbone:        %15" PRId64 "   %10.2f %%  of vars",
         stats.backbone_probes,
         percent (stats.backbone_probes, stats.vars));
    PRT ("   rounds:       %15" PRId64 "   %10.2f    per phase",
         stats.backbone_rounds,
         relative (stats.backbone_rounds, stats.backbone_phases));
    PRT ("   phases:       %15" PRId64 "   %10.2f    interval",
         stats.backbone_phases,
         relative (stats.conflicts, stats.backbone_phases));
    PRT ("   units:        %15" PRId64 "   %10.2f    per phase",
         stats.backbone_units,
         percent (stats.backbone_units, stats.backbone_phases));
  }
  if (all || stats.blocked) {
    PRT ("blocked:         %15" PRId64
         "   %10.2f %%  of irredundant clauses",
         stats.blocked, percent (stats.blocked, stats.clauses_irredundant));
    PRT ("  blockings:     %15" PRId64 "   %10.2f    internal",
         stats.blockings, relative (stats.conflicts, stats.blockings));
    PRT ("  candidates:    %15" PRId64 "   %10.2f    per blocking ",
         stats.blocked_candidates,
         relative (stats.blocked_candidates, stats.blockings));
    PRT ("  blockres:      %15" PRId64 "   %10.2f    per candidate",
         stats.blocked_resolutions,
         relative (stats.blocked_resolutions, stats.blocked_candidates));
    PRT ("  pure:          %15" PRId64 "   %10.2f %%  of all variables",
         stats.vars_all_pure, percent (stats.vars_all_pure, stats.vars));
    PRT ("  pureclauses:   %15" PRId64 "   %10.2f    per pure literal",
         stats.blocked_pure_clauses,
         relative (stats.blocked_pure_clauses, stats.vars_all_pure));
  }
  if (all || stats.conflicts_chrono)
    PRT ("chronological:   %15" PRId64 "   %10.2f %%  of conflicts",
         stats.conflicts_chrono,
         percent (stats.conflicts_chrono, stats.conflicts));
  if (all)
    PRT ("compacts:        %15" PRId64 "   %10.2f    interval",
         stats.compacts, relative (stats.conflicts, stats.compacts));
  if (all || stats.conflicts) {
    PRT ("conflicts:       %15" PRId64 "   %10.2f    per second",
         stats.conflicts, relative (stats.conflicts, t));
    PRT ("  backtracked:   %15" PRId64 "   %10.2f %%  of conflicts",
         stats.backtracked, percent (stats.backtracked, stats.conflicts));
  }
  if (all || stats.incremental_decay) {
    PRT ("inc-decay:       %15" PRId64 "   %10.2f %%   per search",
         stats.incremental_decay,
         percent (stats.incremental_decay, stats.searches));
  }
  if (all || stats.conditionings) {
    PRT ("conditioned:     %15" PRId64
         "   %10.2f %%  of irredundant clauses",
         stats.conditioned,
         percent (stats.conditionings, stats.clauses_irredundant));
    PRT ("  conditionings: %15" PRId64 "   %10.2f    interval",
         stats.conditionings,
         relative (stats.conflicts, stats.conditionings));
    PRT ("  condcands:     %15" PRId64 "   %10.2f    candidate clauses",
         stats.condition_candidates,
         relative (stats.condition_candidates, stats.conditionings));
    PRT ("  condassinit:   %17.1f  %9.2f %%  initial assigned",
         relative (stats.condition_pre_assign, stats.conditionings),
         percent (stats.condition_pre_assign, stats.condition_pre_assign));
    PRT ("  condcondinit:  %17.1f  %9.2f %%  initial condition",
         relative (stats.condition_pre_cond, stats.conditionings),
         percent (stats.condition_pre_cond, stats.condition_pre_assign));
    PRT ("  condautinit:   %17.1f  %9.2f %%  initial autarky",
         relative (stats.condition_pre_autarky, stats.conditionings),
         percent (stats.condition_pre_autarky, stats.condition_pre_assign));
    PRT ("  condassrem:    %17.1f  %9.2f %%  final assigned",
         relative (stats.conditioned_assign, stats.conditioned),
         percent (stats.conditioned_assign, stats.conditioned_initial));
    PRT ("  condcondrem:   %19.3f  %7.2f %%  final conditional",
         relative (stats.conditioned_cond, stats.conditioned),
         percent (stats.conditioned_cond, stats.conditioned_assign));
    PRT ("  condautrem:    %19.3f  %7.2f %%  final autarky",
         relative (stats.conditioned_autarky, stats.conditioned),
         percent (stats.conditioned_autarky, stats.conditioned_assign));
    PRT ("  condprops:     %15" PRId64 "   %10.2f    per candidate",
         stats.condition_propagated,
         relative (stats.condition_propagated, stats.condition_candidates));
  }
  if (all || stats.congruence_gates) {
    PRT ("congruence:      %15" PRId64 "   %10.2f    interval",
         stats.congruence_rounds,
         relative (stats.conflicts, stats.congruence_rounds));
    PRT ("   units:        %15" PRId64 "   %10.2f    per congruent",
         stats.congruence_units,
         relative (stats.congruence_units, stats.congruent));
    PRT ("   cong-and:     %15" PRId64 "   %10.2f    per found gates",
         stats.congruence_ands,
         relative (stats.congruence_ands, stats.congruence_gates));
    PRT ("   cong-ite:     %15" PRId64 "   %10.2f    per found gates",
         stats.congruence_ites,
         relative (stats.congruence_ites, stats.congruence_gates));
    PRT ("   cong-xor:     %15" PRId64 "   %10.2f    per found gates",
         stats.congruence_xors,
         relative (stats.congruence_xors, stats.congruence_gates));
    PRT ("   congruent:    %15" PRId64 "   %10.2f    per round",
         stats.congruent,
         relative (stats.congruence_rounds, stats.congruent));
    PRT ("   unaries:      %15" PRId64 "   %10.2f    per round",
         stats.congruence_unary,
         relative (stats.congruence_rounds, stats.congruence_unary));
    int64_t rewritten = stats.congruence_rw_ands +
                        stats.congruence_rw_xors + stats.congruence_rw_ites;
    PRT ("   rewritten:    %15" PRId64 "   %10.2f    per round", rewritten,
         percent (rewritten, stats.congruence_rounds));
    PRT ("   rewri.-ands:  %15" PRId64 "   %10.2f    per rewritten",
         stats.congruence_rw_ands,
         percent (stats.congruence_rw_ands, rewritten));
    PRT ("   rewri.-xors:  %15" PRId64 "   %10.2f%%   per rewritten",
         stats.congruence_rw_xors,
         percent (stats.congruence_rw_xors, rewritten));
    PRT ("   rewri.-ites:  %15" PRId64 "   %10.2f%%   per rewritten",
         stats.congruence_rw_ites,
         percent (stats.congruence_rw_ites, rewritten));
    PRT ("   subsumed:     %15" PRId64 "   %10.2f%%   per round",
         stats.congruence_subsumed,
         relative (stats.congruence_subsumed, stats.congruence_rounds));
    PRT ("   dummy-ands:   %15" PRId64 "   %10.2f%%   per round",
         stats.congruence_dummy_ands,
         relative (stats.congruence_dummy_ands, stats.congruence_rounds));
  }
  if (all || stats.cover_total) {
    PRT ("covered:         %15" PRId64
         "   %10.2f %%  of irredundant clauses",
         stats.cover_total,
         percent (stats.cover_total, stats.clauses_irredundant));
    PRT ("  coverings:     %15" PRId64 "   %10.2f    interval",
         stats.coverings, relative (stats.conflicts, stats.coverings));
    PRT ("  asymmetric:    %15" PRId64 "   %10.2f %%  of covered clauses",
         stats.cover_asymmetric,
         percent (stats.cover_asymmetric, stats.cover_total));
    PRT ("  blocked:       %15" PRId64 "   %10.2f %%  of covered clauses",
         stats.cover_blocked,
         percent (stats.cover_blocked, stats.cover_total));
  }
  if (all || stats.decisions) {
    PRT ("decisions:       %15" PRId64 "   %10.2f    per second",
         stats.decisions, relative (stats.decisions, t));
    PRT ("  searched:      %15" PRId64 "   %10.2f    per decision",
         stats.decision_searched,
         relative (stats.decision_searched, stats.decisions));
    if (all || stats.decision_random) {
      PRT ("  random phase:  %15" PRId64 "   %10.2f    interval",
           stats.decision_random_phase,
           relative (stats.conflicts, stats.decision_random_phase));
      PRT ("  random decs:   %15" PRId64 "   %10.2f    per phase",
           stats.decision_random,
           relative (stats.decision_random, stats.decision_random_phase));
    }
  }
  if (all || stats.deduplicated) {
    PRT ("deduplicated:    %15" PRId64 "   %10.2f %%  per subsumed",
         stats.deduplicated, percent (stats.deduplicated, stats.subsumed));
    PRT ("  deduplitions:  %15" PRId64 "   %10.2f    interval",
         stats.deduplications,
         relative (stats.conflicts, stats.deduplications));
    PRT ("  dedup-init-rnd:%15" PRId64 "   %10.2f %%  of interval",
         stats.deduplicate_rounds,
         percent (stats.deduplicate_rounds, stats.conflicts));
    PRT ("  dedup-init:    %15" PRId64 "   %10.2f %%  of subsumed",
         stats.deduplicate_init,
         percent (stats.deduplicate_init, stats.deduplicate_init));
  }
  if (all || stats.vars_all_elim) {
    PRT ("eliminated:      %15" PRId64 "   %10.2f %%  of all variables",
         stats.vars_all_elim, percent (stats.vars_all_elim, stats.vars));
    PRT ("  fastelim:      %15" PRId64 "   %10.2f %%  of eliminated",
         stats.vars_all_elim_fast,
         percent (stats.vars_all_elim_fast, stats.vars_all_elim));
    PRT ("  elimphases:    %15" PRId64 "   %10.2f    interval",
         stats.eliminate_phases,
         relative (stats.conflicts, stats.eliminate_phases));
    PRT ("  elimrounds:    %15" PRId64 "   %10.2f    per phase",
         stats.eliminations,
         relative (stats.eliminations, stats.eliminate_phases));
    PRT ("  elimtried:     %15" PRId64 "   %10.2f %%  eliminated",
         stats.eliminate_tried,
         percent (stats.vars_all_elim, stats.eliminate_tried));
    PRT ("  elimgates:     %15" PRId64 "   %10.2f %%  gates per tried",
         stats.eliminate_gates,
         percent (stats.eliminate_gates, stats.eliminate_tried));
    PRT ("  elimequivs:    %15" PRId64 "   %10.2f %%  equivalence gates",
         stats.eliminate_equivalence,
         percent (stats.eliminate_equivalence, stats.eliminate_gates));
    PRT ("  elimands:      %15" PRId64 "   %10.2f %%  and gates",
         stats.eliminate_and,
         percent (stats.eliminate_and, stats.eliminate_gates));
    PRT ("  elimites:      %15" PRId64 "   %10.2f %%  if-then-else gates",
         stats.eliminate_ite,
         percent (stats.eliminate_ite, stats.eliminate_gates));
    PRT ("  elimxors:      %15" PRId64 "   %10.2f %%  xor gates",
         stats.eliminate_xor,
         percent (stats.eliminate_xor, stats.eliminate_gates));
    PRT ("  elimdefs:      %15" PRId64 "   %10.2f %%  definitions",
         stats.eliminate_def_success,
         percent (stats.eliminate_def_success, stats.eliminate_gates));
    PRT ("  elimsubst:     %15" PRId64 "   %10.2f %%  substituted",
         stats.eliminate_substituted,
         percent (stats.eliminate_substituted, stats.vars_all_elim));
    PRT (
        "  elimsubstequi: %15" PRId64 "   %10.2f %%  equivalence gates",
        stats.eliminate_equivalence,
        percent (stats.eliminate_equivalence, stats.eliminate_substituted));
    PRT ("  elimsubstands: %15" PRId64 "   %10.2f %%  and gates",
         stats.eliminated_and,
         percent (stats.eliminated_and, stats.eliminate_substituted));
    PRT ("  elimsubstites: %15" PRId64 "   %10.2f %%  if-then-else gates",
         stats.eliminated_ite,
         percent (stats.eliminated_ite, stats.eliminate_substituted));
    PRT ("  elimsubstxors: %15" PRId64 "   %10.2f %%  xor gates",
         stats.eliminated_xor,
         percent (stats.eliminated_xor, stats.eliminate_substituted));
    PRT ("  elimsubstdefs: %15" PRId64 "   %10.2f %%  definitions",
         stats.eliminated_defs,
         percent (stats.eliminated_defs, stats.eliminate_substituted));
    PRT ("  elimres:       %15" PRId64 "   %10.2f    per eliminated",
         stats.eliminate_resolved,
         relative (stats.eliminate_resolved, stats.vars_all_elim));
    PRT ("  elimrestried:  %15" PRId64 "   %10.2f %%  per resolution",
         stats.eliminate_tried_res,
         percent (stats.eliminate_tried_res, stats.eliminate_resolved));
    PRT ("  def checked:   %15" PRId64 "   %10.2f    per phase",
         stats.eliminate_def_check,
         relative (stats.eliminate_def_check, stats.eliminations));
    PRT ("  def extracted: %15" PRId64 "   %10.2f %%  per checked",
         stats.eliminate_def_success,
         percent (stats.eliminate_def_success, stats.eliminate_def_check));
    PRT ("  def units:     %15" PRId64 "   %10.2f %%  per checked",
         stats.eliminate_def_unit,
         percent (stats.eliminate_def_unit, stats.eliminate_def_check));
  }
  if (all || stats.up_cb) {
    PRT ("ext.prop. calls: %15" PRId64 "   %10.2f %%  of queries",
         stats.up_cb_prop, percent (stats.up_cb_prop, stats.up_cb));
    PRT ("  propagating:   %15" PRId64 "   %10.2f %%  per eprop-call",
         stats.up_cb_prop_assign,
         percent (stats.up_cb_prop_assign, stats.up_cb_prop));
    PRT ("  explained:     %15" PRId64 "   %10.2f %%  per eprop-call",
         stats.up_cb_prop_explain,
         percent (stats.up_cb_prop_explain, stats.up_cb_prop));
    PRT ("  falsified:     %15" PRId64 "   %10.2f %%  per eprop-call",
         stats.up_cb_prop_clash,
         percent (stats.up_cb_prop_clash, stats.up_cb_prop_clash));
    PRT ("ext.clause calls:%15" PRId64 "   %10.2f %%  of queries",
         stats.up_cb_add, percent (stats.up_cb_add, stats.up_cb));
    PRT ("  learned:       %15" PRId64 "   %10.2f %%  per called",
         stats.up_learn, percent (stats.up_learn, stats.up_cb_add));
    PRT ("  conflicting:   %15" PRId64 "   %10.2f %%  per learned",
         stats.up_learn_conflict,
         percent (stats.up_learn_conflict, stats.up_learn));
    PRT ("  propagating:   %15" PRId64 "   %10.2f %%  per learned",
         stats.up_learn_propagating,
         percent (stats.up_learn_propagating, stats.up_learn));
    PRT ("ext.final check: %15" PRId64 "   %10.2f %%  of queries",
         stats.up_cb_check_model,
         percent (stats.up_cb_check_model, stats.up_cb));
  }
  if (all || stats.factored) {
    PRT ("factored:        %15" PRId64 "   %10.2f %%  of variables",
         stats.factored, percent (stats.factored, internal->max_var));
    PRT ("  ands:          %15" PRId64 "   %10.2f %%  of factored",
         stats.factored_and, percent (stats.factored_and, stats.factored));
    PRT ("  xors:          %15" PRId64 "   %10.2f %%  of factored",
         stats.factored_xor, percent (stats.factored_xor, stats.factored));
    PRT ("  ites:          %15" PRId64 "   %10.2f %%  of factored",
         stats.factored_ite, percent (stats.factored_ite, stats.factored));
    PRT ("  eliminated:    %15" PRId64 "   %10.2f %%  of factored",
         stats.factored_eliminated,
         percent (stats.factored_eliminated, stats.factored));
    PRT ("  factor:        %15" PRId64 "   %10.2f    conflict interval",
         stats.factorings, relative (stats.conflicts, stats.factorings));
    PRT ("  cls factored:  %15" PRId64 "   %10.2f    per factored",
         stats.factor_added_clauses,
         relative (stats.factor_added_clauses, factored));
    PRT ("  lits factored: %15" PRId64 "   %10.2f    per factored",
         stats.factor_added_literals,
         relative (stats.factor_added_literals, factored));
    PRT ("  cls unfactored:%15" PRId64 "   %10.2f    per factored",
         stats.factor_removed_irr,
         relative (stats.factor_removed_irr, factored));
    PRT ("  cls redundant: %15" PRId64 "   %10.2f %%  of unfactored",
         stats.factor_removed_red,
         percent (stats.factor_removed_red, stats.factor_removed_irr));
    PRT ("  lits unfactored:%14" PRId64 "   %10.2f    per factored",
         stats.factor_removed_lits,
         relative (stats.factor_removed_lits, factored));
  }
  if (all || stats.vars_all_fixed) {
    PRT ("fixed:           %15" PRId64 "   %10.2f %%  of all variables",
         stats.vars_all_fixed, percent (stats.vars_all_fixed, stats.vars));
    PRT ("  failed:        %15" PRId64 "   %10.2f %%  of all variables",
         stats.failed_literals,
         percent (stats.failed_literals, stats.vars));
    PRT ("  probefailed:   %15" PRId64 "   %10.2f %%  per failed",
         stats.probe_failed_literals,
         percent (stats.probe_failed_literals, stats.failed_literals));
    PRT ("  transredunits: %15" PRId64 "   %10.2f %%  per failed",
         stats.transitive_units,
         percent (stats.transitive_units, stats.failed_literals));
    PRT ("  inprobephases: %15" PRId64 "   %10.2f    interval",
         stats.inprobingphases,
         relative (stats.conflicts, stats.inprobingphases));
    PRT ("  inprobesuccess:%15" PRId64 "   %10.2f %%  phases",
         stats.inprobingsuccess,
         percent (stats.inprobingsuccess, stats.inprobingphases));
    PRT ("  probingrounds: %15" PRId64 "   %10.2f    per phase",
         stats.probingrounds,
         relative (stats.probingrounds, stats.inprobingphases));
    PRT ("  probed:        %15" PRId64 "   %10.2f    per failed",
         stats.probed, relative (stats.probed, stats.failed_literals));
    PRT ("  hbrs:          %15" PRId64 "   %10.2f    per probed",
         stats.hbrs, relative (stats.hbrs, stats.probed));
    PRT ("  hbrsizes:      %15" PRId64 "   %10.2f    per hbr",
         stats.hbr_sizes, relative (stats.hbr_sizes, stats.hbrs));
    PRT ("  hbreds:        %15" PRId64 "   %10.2f %%  per hbr",
         stats.hbr_redundant, percent (stats.hbr_redundant, stats.hbrs));
    PRT ("  hbrsubs:       %15" PRId64 "   %10.2f %%  per hbr",
         stats.hbr_subsuming, percent (stats.hbr_subsuming, stats.hbrs));
  }
  PRT ("  units:         %15" PRId64 "   %10.2f    interval",
       stats.learned_units,
       relative (stats.conflicts, stats.learned_units));
  PRT ("  binaries:      %15" PRId64 "   %10.2f    interval",
       stats.learned_binaries,
       relative (stats.conflicts, stats.learned_binaries));
  if (all || stats.flush_learned) {
    PRT ("flushed:         %15" PRId64 "   %10.2f %%  per conflict",
         stats.flush_learned,
         percent (stats.flush_learned, stats.conflicts));
    PRT ("  hyper:         %15" PRId64 "   %10.2f %%  per conflict",
         stats.flush_hyper, relative (stats.flush_hyper, stats.conflicts));
    PRT ("  flushings:     %15" PRId64 "   %10.2f    interval",
         stats.flushings, relative (stats.conflicts, stats.flushings));
  }
  if (all || stats.instantiated) {
    PRT ("instantiated:    %15" PRId64 "   %10.2f %%  of tried",
         stats.instantiated,
         percent (stats.instantiated, stats.instantiate_tried));
    PRT ("  instrounds:    %15" PRId64 "   %10.2f %%  of elimrounds",
         stats.instantiations,
         percent (stats.instantiations, stats.eliminations));
  }
  if (all || stats.conflicts) {
    PRT ("learned:         %15" PRId64 "   %10.2f %%  per conflict",
         stats.learned_clauses,
         percent (stats.learned_clauses, stats.conflicts));
    PRT ("  bumped:        %15" PRId64 "   %10.2f    per learned",
         stats.vars_bumped,
         relative (stats.vars_bumped, stats.learned_clauses));
    PRT ("  recomputed:    %15" PRId64 "   %10.2f %%  per learned",
         stats.clause_recompute_glue,
         percent (stats.clause_recompute_glue, stats.learned_clauses));
    PRT ("  promoted1:     %15" PRId64 "   %10.2f %%  per learned",
         stats.clause_promoted_tier1,
         percent (stats.clause_promoted_tier1, stats.learned_clauses));
    PRT ("  promoted2:     %15" PRId64 "   %10.2f %%  per learned",
         stats.clause_promoted_tier2,
         percent (stats.clause_promoted_tier2, stats.learned_clauses));
    PRT ("  improvedglue:  %15" PRId64 "   %10.2f %%  per learned",
         stats.clause_improved_glue,
         percent (stats.clause_improved_glue, stats.learned_clauses));
  }
  if (all || stats.lucky) {
    PRT ("lucky:           %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky, percent (stats.lucky, stats.lucky_tried));
    PRT ("  constantzero   %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky_constant_zero,
         percent (stats.lucky_constant_zero, stats.lucky_tried));
    PRT ("  constantone    %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky_constant_one,
         percent (stats.lucky_constant_one, stats.lucky_tried));
    PRT ("  backwardone    %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky_backward_one,
         percent (stats.lucky_backward_one, stats.lucky_tried));
    PRT ("  backwardzero   %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky_backward_zero,
         percent (stats.lucky_backward_zero, stats.lucky_tried));
    PRT ("  forwardone     %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky_forward_one,
         percent (stats.lucky_forward_one, stats.lucky_tried));
    PRT ("  forwardzero    %15" PRId64 "   %10.2f %%  of tried",
         stats.lucky_forward_zero,
         percent (stats.lucky_forward_zero, stats.lucky_tried));
    PRT ("  units:         %15" PRId64 "   %10.2f    of tried",
         stats.lucky_units,
         relative (stats.lucky_units, stats.lucky_tried));
  }
  PRT ("  extendbytes:   %15zd   %10.2f    bytes and MB", extendbytes,
       extendbytes / (double) (1l << 20));
  if (all || stats.learned_clauses)
    PRT ("learned_lits:    %15" PRId64 "   %10.2f %%  learned literals",
         stats.learned_literals,
         percent (stats.learned_literals, stats.learned_literals));
  PRT ("minimized:       %15" PRId64 "   %10.2f %%  learned literals",
       stats.minimized, percent (stats.minimized, stats.learned_literals));
  PRT ("shrunken:        %15" PRId64 "   %10.2f %%  learned literals",
       stats.shrunken, percent (stats.shrunken, stats.learned_literals));
  PRT ("minishrunken:    %15" PRId64 "   %10.2f %%  learned literals",
       stats.shrunken_minimize,
       percent (stats.shrunken_minimize, stats.learned_literals));

  if (all || stats.conflicts) {
    PRT ("otfs:            %15" PRId64 "   %10.2f %%  of conflict",
         stats.otfs_subsumed + stats.otfs_strengthened,
         percent (stats.otfs_subsumed + stats.otfs_strengthened,
                  stats.conflicts));
    PRT ("  subsumed       %15" PRId64 "   %10.2f %%  of conflict",
         stats.otfs_subsumed,
         percent (stats.otfs_subsumed, stats.conflicts));
    PRT ("  strengthened   %15" PRId64 "   %10.2f %%  of conflict",
         stats.otfs_strengthened,
         percent (stats.otfs_strengthened, stats.conflicts));
  }

  PRT ("propagations:    %15" PRId64 "   %10.2f M  per second",
       propagations, relative (propagations / 1e6, t));
  PRT ("  coverprops:    %15" PRId64 "   %10.2f %%  of propagations",
       stats.propagations_cover,
       percent (stats.propagations_cover, propagations));
  PRT ("  probeprops:    %15" PRId64 "   %10.2f %%  of propagations",
       stats.propagations_probe,
       percent (stats.propagations_probe, propagations));
  PRT ("  searchprops:   %15" PRId64 "   %10.2f %%  of propagations",
       stats.propagations_search,
       percent (stats.propagations_search, propagations));
  PRT ("  transredprops: %15" PRId64 "   %10.2f %%  of propagations",
       stats.propagations_transred,
       percent (stats.propagations_transred, propagations));
  PRT ("  vivifyprops:   %15" PRId64 "   %10.2f %%  of propagations",
       stats.propagations_vivify,
       percent (stats.propagations_vivify, propagations));
  if (all || stats.vars_reactivated) {
    PRT ("reactivated:     %15" PRId64 "   %10.2f %%  of all variables",
         stats.vars_reactivated,
         percent (stats.vars_reactivated, stats.vars));
  }
  if (all || stats.reduced) {
    PRT ("reduced:         %15" PRId64 "   %10.2f %%  per conflict",
         stats.reduced, percent (stats.reduced, stats.conflicts));
    PRT ("  reductions:    %15" PRId64 "   %10.2f    interval",
         stats.reductions, relative (stats.conflicts, stats.reductions));
    PRT ("  collections:   %15" PRId64 "   %10.2f    interval",
         stats.collections, relative (stats.conflicts, stats.collections));
  }
  if (all || stats.rephased) {
    PRT ("rephased:        %15" PRId64 "   %10.2f    interval",
         stats.rephased, relative (stats.conflicts, stats.rephased));
    PRT ("  rephasedbest:  %15" PRId64 "   %10.2f %%  rephased best",
         stats.rephased_best,
         percent (stats.rephased_best, stats.rephased));
    PRT ("  rephasedflip:  %15" PRId64 "   %10.2f %%  rephased flipping",
         stats.rephased_flipped,
         percent (stats.rephased_flipped, stats.rephased));
    PRT ("  rephasedinv:   %15" PRId64 "   %10.2f %%  rephased inverted",
         stats.rephased_inverted,
         percent (stats.rephased_inverted, stats.rephased));
    PRT ("  rephasedorig:  %15" PRId64 "   %10.2f %%  rephased original",
         stats.rephased_original,
         percent (stats.rephased_original, stats.rephased));
    PRT ("  rephasedrand:  %15" PRId64 "   %10.2f %%  rephased random",
         stats.rephased_random,
         percent (stats.rephased_random, stats.rephased));
    PRT ("  rephasedwalk:  %15" PRId64 "   %10.2f %%  rephased walk",
         stats.rephased_walk,
         percent (stats.rephased_walk, stats.rephased));
  }
  if (all)
    PRT ("rescored:        %15" PRId64 "   %10.2f    interval",
         stats.scores_rescored,
         relative (stats.conflicts, stats.scores_rescored));
  if (all || stats.restart) {
    PRT ("restarts:        %15" PRId64 "   %10.2f    interval",
         stats.restart, relative (stats.conflicts, stats.restart));
    PRT ("  reused:        %15" PRId64 "   %10.2f %%  per restart",
         stats.reused, percent (stats.reused, stats.restart));
    PRT ("  reusedlevels:  %15" PRId64 "   %10.2f %%  per restart levels",
         stats.reused_levels,
         percent (stats.reused_levels, stats.restart_levels));
  }
  if (all || stats.restored_clauses) {
    PRT ("restored:        %15" PRId64 "   %10.2f %%  per weakened",
         stats.restored_clauses,
         percent (stats.restored_clauses, stats.weakened));
    PRT ("  restorations:  %15" PRId64 "   %10.2f %%  per extension",
         stats.restorations,
         percent (stats.restorations, stats.extensions));
    PRT ("  literals:      %15" PRId64 "   %10.2f    per restored clause",
         stats.restored_literals,
         relative (stats.restored_literals, stats.restored_clauses));
  }
  if (all || stats.stable_phases_total) {
    PRT ("stabilizing:     %15" PRId64 "   %10.2f %%  of conflicts",
         stats.stable_phases_total,
         percent (stats.stable_conflicts, stats.conflicts));
    PRT ("  restartstab:   %15" PRId64 "   %10.2f %%  of all restarts",
         stats.restart_stable,
         percent (stats.restart_stable, stats.restart));
    PRT ("  reusedstab:    %15" PRId64 "   %10.2f %%  per stable restarts",
         stats.reused_stable,
         percent (stats.reused_stable, stats.restart_stable));
  }
  if (all || stats.vars_all_substituted) {
    PRT ("substituted:     %15" PRId64 "   %10.2f %%  of all variables",
         stats.vars_all_substituted,
         percent (stats.vars_all_substituted, stats.vars));
    PRT ("  decompositions:%15" PRId64 "   %10.2f    per phase",
         stats.decompositions,
         relative (stats.decompositions, stats.inprobingphases));
  }
  if (all || stats.sweep_eq) {
    PRT ("sweep equivs:    %15" PRId64 "   %10.2f %%  of swept variables",
         stats.sweep_eq, percent (stats.sweep_eq, stats.sweep_variables));
    PRT ("  sweepings:     %15" PRId64 "   %10.2f    vars per sweeping",
         stats.sweepings,
         relative (stats.sweep_variables, stats.sweepings));
    PRT ("  swept vars:    %15" PRId64 "   %10.2f %%  of all variables",
         stats.sweep_variables,
         percent (stats.sweep_variables, stats.vars));
    PRT ("  sweep units:   %15" PRId64 "   %10.2f %%  of all variables",
         stats.sweep_units, percent (stats.sweep_units, stats.vars));
    PRT ("  solved:        %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_solved,
         relative (stats.sweep_solved, stats.sweep_variables));
    PRT ("  sat:           %15" PRId64 "   %10.2f %%  solved",
         stats.sweep_solved_sat,
         percent (stats.sweep_solved_sat, stats.sweep_solved));
    PRT ("  unsat:         %15" PRId64 "   %10.2f %%  solved",
         stats.sweep_solved_unsat,
         percent (stats.sweep_solved_unsat, stats.sweep_solved));
    PRT ("  backbone solved:%14" PRId64 "   %10.2f %%  solved",
         stats.sweep_bb_solved,
         percent (stats.sweep_bb_solved, stats.sweep_solved));
    PRT ("    sat:         %15" PRId64 "   %10.2f %%  backbone solved",
         stats.sweep_bb_solved_sat,
         percent (stats.sweep_bb_solved_sat, stats.sweep_bb_solved));
    PRT ("    unsat:       %15" PRId64 "   %10.2f %%  backbone solved",
         stats.sweep_bb_solved_unsat,
         percent (stats.sweep_bb_solved_unsat, stats.sweep_bb_solved));
    PRT ("    unknown:     %15" PRId64 "   %10.2f %%  backbone solved",
         stats.sweep_bb_solved_to,
         percent (stats.sweep_bb_solved_to, stats.sweep_bb_solved));
    PRT ("    fixed:       %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_bb_fixed,
         relative (stats.sweep_bb_fixed, stats.sweep_variables));
    PRT ("    flip:        %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_bb_flip,
         relative (stats.sweep_bb_flip, stats.sweep_variables));
    PRT ("    flipped:     %15" PRId64 "   %10.2f %%  of backbone flip",
         stats.sweep_bb_flipped,
         percent (stats.sweep_bb_flipped, stats.sweep_bb_flip));
    PRT ("  equiv solved:  %15" PRId64 "   %10.2f %%  solved",
         stats.sweep_eq_solved,
         percent (stats.sweep_eq_solved, stats.sweep_solved));
    PRT ("    sat:         %15" PRId64 "   %10.2f %%  equiv solved",
         stats.sweep_eq_solved_sat,
         percent (stats.sweep_eq_solved_sat, stats.sweep_eq_solved));
    PRT ("    unsat:       %15" PRId64 "   %10.2f %%  equiv solved",
         stats.sweep_eq_solved_unsat,
         percent (stats.sweep_eq_solved_unsat, stats.sweep_eq_solved));
    PRT ("    unknown:     %15" PRId64 "   %10.2f %%  equiv solved",
         stats.sweep_eq_solved_to,
         percent (stats.sweep_eq_solved_to, stats.sweep_eq_solved));
    PRT ("    flip:        %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_eq_flip,
         relative (stats.sweep_eq_flip, stats.sweep_variables));
    PRT ("    flipped:     %15" PRId64 "   %10.2f %%  of equiv flip",
         stats.sweep_eq_flipped,
         percent (stats.sweep_eq_flipped, stats.sweep_eq_flip));
    PRT ("  depth:         %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_depth,
         relative (stats.sweep_depth, stats.sweep_variables));
    PRT ("  environment:   %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_environment,
         relative (stats.sweep_environment, stats.sweep_variables));
    PRT ("  clauses:       %15" PRId64 "   %10.2f    per swept variable",
         stats.sweep_clauses,
         relative (stats.sweep_clauses, stats.sweep_variables));
    PRT ("  completed:     %15" PRId64 "   %10.2f    sweeps to complete",
         stats.sweep_completed,
         relative (stats.sweepings, stats.sweep_completed));
  }
  if (all || stats.subsumed) {
    PRT ("subsumed:        %15" PRId64 "   %10.2f %%  of all clauses",
         stats.subsumed,
         percent (stats.subsumed, stats.clauses));
    PRT ("  subsumephases: %15" PRId64 "   %10.2f    interval",
         stats.subsume_phases,
         relative (stats.conflicts, stats.subsume_phases));
    PRT ("  subsumerounds: %15" PRId64 "   %10.2f    per phase",
         stats.subsume_rounds,
         relative (stats.subsume_rounds, stats.subsume_phases));
    PRT ("  transreds:     %15" PRId64 "   %10.2f    interval",
         stats.transitive_rounds,
         relative (stats.conflicts, stats.transitive_rounds));
    PRT ("  transitive:    %15" PRId64 "   %10.2f %%  per subsumed",
         stats.transitive_clauses,
         percent (stats.transitive_clauses, stats.subsumed));
    PRT ("  subirr:        %15" PRId64 "   %10.2f %%  of subsumed",
         stats.subsumed_irredundant,
         percent (stats.subsumed_irredundant, stats.subsumed));
    PRT ("  subred:        %15" PRId64 "   %10.2f %%  of subsumed",
         stats.subsumed_redundant,
         percent (stats.subsumed_redundant, stats.subsumed));
    PRT ("  subtried:      %15" PRId64 "   %10.2f    tried per subsumed",
         stats.subsume_tried,
         relative (stats.subsume_tried, stats.subsumed));
    PRT ("  subchecks:     %15" PRId64 "   %10.2f    per tried",
         stats.subsume_checks,
         relative (stats.subsume_checks, stats.subsume_tried));
    PRT ("  subchecks2:    %15" PRId64 "   %10.2f %%  per subcheck",
         stats.subsume_checks_binary,
         percent (stats.subsume_checks_binary, stats.subsume_checks));
    PRT ("  elimotfsub:    %15" PRId64 "   %10.2f %%  of subsumed",
         stats.eliminate_otf_sub,
         percent (stats.eliminate_otf_sub, stats.subsumed));
    PRT ("  elimbwsub:     %15" PRId64 "   %10.2f %%  of subsumed",
         stats.eliminate_subsumed_bw,
         percent (stats.eliminate_subsumed_bw, stats.subsumed));
    PRT ("  eagersub:      %15" PRId64 "   %10.2f %%  of subsumed",
         stats.eager_subsumed,
         percent (stats.eager_subsumed, stats.subsumed));
    PRT ("  eagertried:    %15" PRId64 "   %10.2f    tried per eagersub",
         stats.eager_subsumptions,
         relative (stats.eager_subsumptions, stats.eager_subsumed));
  }
  if (all || stats.strengthened) {
    PRT ("strengthened:    %15" PRId64 "   %10.2f %%  of all clauses",
         stats.strengthened,
         percent (stats.strengthened, stats.clauses));
    PRT ("  elimotfstr:    %15" PRId64 "   %10.2f %%  of strengthened",
         stats.eliminate_otf_str,
         percent (stats.eliminate_otf_str, stats.strengthened));
    PRT ("  elimbwstr:     %15" PRId64 "   %10.2f %%  of strengthened",
         stats.eliminate_strength_bw,
         percent (stats.eliminate_strength_bw, stats.strengthened));
  }
  if (all || stats.ternary_htrs) {
    PRT ("ternary:         %15" PRId64 "   %10.2f %%  of resolved",
         stats.ternary_htrs,
         percent (stats.ternary_htrs, stats.ternary_resolutions));
    PRT ("  phases:        %15" PRId64 "   %10.2f    interval",
         stats.ternary, relative (stats.conflicts, stats.ternary));
    PRT ("  htr3:          %15" PRId64
         "   %10.2f %%  ternary hyper ternres",
         stats.ternary_htrs_ternary,
         percent (stats.ternary_htrs_ternary, stats.ternary_htrs));
    PRT ("  htr2:          %15" PRId64 "   %10.2f %%  binary hyper ternres",
         stats.ternary_htrs_binary,
         percent (stats.ternary_htrs_binary, stats.ternary_htrs));
  }
  PRT ("ticks:           %15" PRId64 "   %10.2f    propagation", totalticks,
       relative (totalticks, stats.propagations_search));
  PRT (" searchticks:    %15" PRId64 "   %10.2f %%  totalticks",
       searchticks, percent (searchticks, totalticks));
  PRT ("   stableticks:  %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_search_stable,
       percent (stats.ticks_search_stable, searchticks));
  PRT ("   unstableticks:%15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_search_unstable,
       percent (stats.ticks_search_unstable, searchticks));
  PRT (" inprobeticks:   %15" PRId64 "   %10.2f %%  totalticks",
       inprobeticks, percent (inprobeticks, totalticks));
  PRT ("   backboneticks:%15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_backbone, percent (stats.ticks_backbone, searchticks));
  PRT ("   factorticks:  %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_factor, percent (stats.ticks_factor, searchticks));
  PRT ("   probeticks:   %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_probe, percent (stats.ticks_probe, searchticks));
  PRT ("   sweepticks:   %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_sweep, percent (stats.ticks_sweep, searchticks));
  PRT ("   ternaryticks: %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_ternary, percent (stats.ticks_ternary, searchticks));
  PRT ("   vivifyticks:  %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_vivify, percent (stats.ticks_vivify, searchticks));
  PRT ("   walkticks:    %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_walk, percent (stats.ticks_walk, searchticks));
  PRT ("   walkflipticks:%15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_walk_flip, percent (stats.ticks_walk_flip, searchticks));
  PRT ("   walkflipbrk:  %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_walk_flip_broke,
       percent (stats.ticks_walk_flip_broke, searchticks));
  PRT ("   walkflipWL:   %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_walk_flip_wl,
       percent (stats.ticks_walk_flip_wl, searchticks));
  PRT ("   walkpickticks:%15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_walk_pick, percent (stats.ticks_walk_pick, searchticks));
  PRT ("   walkbreak:    %15" PRId64 "   %10.2f %%  searchticks",
       stats.ticks_walk_break,
       percent (stats.ticks_walk_break, searchticks));
  if (all) {
    PRT ("tier recomputed: %15" PRId64 "   %10.2f    interval",
         stats.recomputed_tiers,
         relative (stats.conflicts, stats.recomputed_tiers));
  }
  if (all || stats.ilb_triggers) {
    PRT ("trail reuses:    %15" PRId64 "   %10.2f %%  of incremental calls",
         stats.ilb_success,
         percent (stats.ilb_success, stats.ilb_triggers));
    PRT ("  levels:        %15" PRId64 "   %10.2f    per reuse",
         stats.ilb_reuse_levels,
         relative (stats.ilb_reuse_levels, stats.ilb_success));
    PRT ("  literals:      %15" PRId64 "   %10.2f    per reuse",
         stats.ilb_reuse_literals,
         relative (stats.ilb_reuse_literals, stats.ilb_success));
    PRT ("  assumptions:   %15" PRId64 "   %10.2f    per reuse",
         stats.ilb_reuse_assumptions,
         relative (stats.ilb_reuse_assumptions, stats.ilb_success));
  }
  if (all || vivified) {
    PRT ("vivified:        %15" PRId64 "   %10.2f %%  of all clauses",
         vivified, percent (vivified, stats.clauses));
    PRT ("  vivifications: %15" PRId64 "   %10.2f    interval",
         stats.vivifications,
         relative (stats.conflicts, stats.vivifications));
    PRT ("  vivifychecks:  %15" PRId64 "   %10.2f %%  per conflict",
         stats.vivify_checks,
         percent (stats.vivify_checks, stats.conflicts));
    const int64_t vivified = stats.vivified_tier1 + stats.vivified_tier2 +
                             stats.vivified_tier3 + stats.vivified_irr;
    PRT ("  vivified:      %15" PRId64 "   %10.2f %%  per check", vivified,
         percent (vivified, stats.vivify_checks));
    PRT ("  vified-irred:  %15" PRId64 "   %10.2f %%  per vivified",
         stats.vivified_irr, percent (stats.vivified_irr, vivified));
    PRT ("  vified-tier1:  %15" PRId64 "   %10.2f %%  per vivified",
         stats.vivified_tier1, percent (stats.vivified_tier1, vivified));
    PRT ("  vified-tier2:  %15" PRId64 "   %10.2f %%  per vivified",
         stats.vivified_tier2, percent (stats.vivified_tier2, vivified));
    PRT ("  vified-tier3:  %15" PRId64 "   %10.2f %%  per vivified",
         stats.vivified_tier3, percent (stats.vivified_tier3, vivified));
    PRT ("  vivifysched:   %15" PRId64 "   %10.2f %%  checks per scheduled",
         stats.vivify_scheduled,
         percent (stats.vivify_checks, stats.vivify_scheduled));
    PRT ("  vivifyunits:   %15" PRId64 "   %10.2f %%  per vivify check",
         stats.vivify_units,
         percent (stats.vivify_units, stats.vivify_checks));
    PRT ("  vivifyinst:    %15" PRId64 "   %10.2f %%  per vivify check",
         stats.vivify_instantiated,
         percent (stats.vivify_instantiated, stats.vivify_checks));
    PRT ("  vivifysubs:    %15" PRId64 "   %10.2f %%  per subsumed",
         stats.vivify_subsumed,
         percent (stats.vivify_subsumed, stats.subsumed));
    PRT ("  vivifyflushed: %15" PRId64 "   %10.2f %%  per subsumed",
         stats.vivify_flushed,
         percent (stats.vivify_flushed, stats.subsumed));
    PRT ("  vivifysubred:  %15" PRId64 "   %10.2f %%  per subs",
         stats.vivify_subsumed_red,
         percent (stats.vivify_subsumed_red, stats.vivify_subsumed));
    PRT ("  vivifysubirr:  %15" PRId64 "   %10.2f %%  per subs",
         stats.vivify_subsumed_irr,
         percent (stats.vivify_subsumed_irr, stats.vivify_subsumed));
    PRT ("  vivifystrs:    %15" PRId64 "   %10.2f %%  per strengthened",
         stats.vivify_strength,
         percent (stats.vivify_strength, stats.strengthened));
    PRT ("  vivifystrirr:  %15" PRId64 "   %10.2f %%  per vivifystrs",
         stats.vivify_strength_irr,
         percent (stats.vivify_strength_irr, stats.vivify_strength));
    PRT ("  vivifystred1:  %15" PRId64 "   %10.2f %%  per vivifystrs",
         stats.vivify_strength_tier1,
         percent (stats.vivify_strength_tier1, stats.vivify_strength));
    PRT ("  vivifystred2:  %15" PRId64 "   %10.2f %%  per viviyfstrs",
         stats.vivify_strength_tier2,
         percent (stats.vivify_strength_tier2, stats.vivify_strength));
    PRT ("  vivifystred3:  %15" PRId64 "   %10.2f %%  per vivifystrs",
         stats.vivify_strength_tier3,
         percent (stats.vivify_strength_tier3, stats.vivify_strength));
    PRT ("  vivifydemote:  %15" PRId64 "   %10.2f %%  per vivifystrs",
         stats.vivify_demote,
         percent (stats.vivify_demote, stats.vivify_strength));
    PRT ("  vivifydecs:    %15" PRId64 "   %10.2f    per checks",
         stats.vivify_decisions,
         relative (stats.vivify_decisions, stats.vivify_checks));
    PRT ("  vivifyreused:  %15" PRId64
         "   %10.2f %%  per non-reused decision",
         stats.vivify_reused,
         percent (stats.vivify_reused, stats.vivify_decisions));
  }
  if (all || stats.walk) {
    PRT ("walked:          %15" PRId64 "   %10.2f    interval", stats.walk,
         relative (stats.conflicts, stats.walk));
    if (all || stats.walk_warmup) {
      PRT ("  prop-warmup:   %15" PRId64 "   %10.2f    per warmup",
           stats.walk_warmup_propagate,
           relative (stats.walk_warmup_propagate, stats.walk_warmup));
      PRT ("  dec-warmup:    %15" PRId64 "   %10.2f    per warmup",
           stats.walk_warmup_decision,
           relative (stats.walk_warmup_decision, stats.walk_warmup));
      PRT ("  dummydec-w:    %15" PRId64 "   %10.2f    per warmup",
           stats.walk_warmup_dummy,
           relative (stats.walk_warmup_dummy, stats.walk_warmup));
      PRT ("  conflicts:     %15" PRId64 "   %10.2f    per warmup",
           stats.walk_warmup_conflicts,
           relative (stats.walk_warmup_conflicts, stats.walk_warmup));
      PRT ("  warmup:        %15" PRId64 "   %10.2f    per walk",
           stats.walk_warmup, relative (stats.walk_warmup, stats.walk));
    }
#ifndef QUIET
    if (internal->profiles.walk.value > 0) {
      PRT ("  flips:         %15" PRId64 "   %10.2f M  per second",
           stats.walk_flips,
           relative (1e-6 * stats.walk_flips,
                     internal->profiles.walk.value));
      PRT ("  ddfwflips:     %15" PRId64 "   %10.2f M  per second",
           stats.walk_ddfw_flips,
           relative (1e-6 * stats.walk_ddfw_flips,
                     internal->profiles.walk.value));
    }
    else
#endif
    {
      PRT ("  flips:         %15" PRId64 "   %10.2f    per walk",
           stats.walk_flips, relative (stats.walk_flips, stats.walk));
      PRT ("  ddfwflips:     %15" PRId64 "   %10.2f    per walk",
           stats.walk_ddfw_flips, relative (stats.walk_ddfw_flips, stats.walk));
    }
    if (stats.walk_minimum < INT64_MAX)
      PRT ("  minimum:       %15" PRId64 "   %10.2f %%  clauses",
           stats.walk_minimum,
           percent (stats.walk_minimum, stats.clauses_irredundant));
    PRT ("  broken:        %15" PRId64 "   %10.2f    per flip",
         stats.walk_broken, relative (stats.walk_broken, stats.walk_flips));
    PRT ("  improved:      %15" PRId64 "   %10.2f    per walk",
         stats.walk_improved, relative (stats.walk_improved, stats.walk));
    PRT ("  wrv-flip:      %15" PRId64 "   %10.2f %% flip",
         stats.walk_flips_reducing,
         percent (stats.walk_flips_reducing, stats.walk_flips));
    PRT ("  side-flip:     %15" PRId64 "   %10.2f %% flip",
         stats.walk_flips_sideways,
         percent (stats.walk_flips_sideways, stats.walk_flips));
    PRT ("  wght-transfer: %15" PRId64 "   %10.2f %% flip",
         stats.walk_flips_transfer,
         percent (stats.walk_flips_transfer, stats.walk_flips));
  }
  if (all || stats.weakened) {
    PRT ("weakened:        %15" PRId64 "   %10.2f    average size",
         stats.weakened, relative (stats.weakened_lengths, stats.weakened));
    PRT ("  extensions:    %15" PRId64 "   %10.2f    interval",
         stats.extensions, relative (stats.conflicts, stats.extensions));
    PRT ("  flipped:       %15" PRId64 "   %10.2f    per weakened",
         stats.extended, relative (stats.extended, stats.weakened));
  }
}

// Names are shortened to be 21 chars (22 with ':')
// absolute numbers may be higher then 15 (should be rare though)
// REF_OFFSET is 12 for old stat format but that spills over
// PREFIX, NAME, SPACE, NUM, SPACE, REF, SPACE, SYMBOL, SPACE, PRINT
// 2 + 22 + 1 + 15 + 1 + 11 + 1 + 3 + 1 + 21 = 80
#define NAME_OFFSET "22"
#define NUM_OFFSET "15"
#define REF_OFFSET "11.2"
#define SYMBOL_OFFSET "3"
#define PRINT_OFFSET "21"

#define SECONDS(FIRST, IGNORE) relative (FIRST, t)
#define INTERVAL(FIRST, IGNORE) relative (stats.conflicts, FIRST)
#define NOTHING(FIRST, IGNORE) 0

#define PRINT_STATER(NAME, NUM, VERBOSE, OTHER_NUM, SYMBOL, PRINT) \
  do { \
    if (VERBOSE > 1 && VERBOSE > verbose) \
      break; \
    if (VERBOSE == 1 && !NUM && VERBOSE > verbose) \
      break; \
    const double RELATIVE = OTHER_NUM; \
    const char *SAVED_SYMBOL = (const char *) (SYMBOL); \
    const char *SAVED_PRINT = (const char *) (PRINT); \
    if (SYMBOL == 0) \
      MSG ("%-" NAME_OFFSET "s %" NUM_OFFSET PRId64, NAME ":", NUM); \
    else \
      MSG ("%-" NAME_OFFSET "s %" NUM_OFFSET PRId64 " %" REF_OFFSET \
           "f %-" SYMBOL_OFFSET "s %-" PRINT_OFFSET "s", \
           NAME ":", NUM, RELATIVE, SAVED_SYMBOL, SAVED_PRINT); \
  } while (0)

void Stats::print_new (Internal *internal) {

  Stats stats = internal->stats;
  int verbose = internal->opts.verbose;

  // TODO: verbosity is always 3 like this.
  if (internal->opts.stats == 3)
    verbose = 2;
#ifdef LOGGING
  if (internal->opts.log)
    verbose = 3;
#endif // ifdef LOGGING

  double t = internal->solve_time ();

#define STATISTIC(NAME, VERBOSE, COMMAND, SYMBOL, OTHER) \
  PRINT_STATER (#NAME, stats.NAME, VERBOSE, \
                COMMAND (stats.NAME, stats.OTHER), SYMBOL, #OTHER);

  CADICAL_STATISTICS

#undef STATISTIC
}
#endif

void Stats::print (Internal *internal) {

#ifdef QUIET
  (void) internal;
#else

  if (internal->opts.profile)
    internal->print_profile ();

  SECTION ("statistics");

  if (internal->opts.stats > 1)
    print_new (internal);
  else
    print_old (internal);

  LINE ();
  MSG ("%sseconds are measured in %s time for solving%s",
       tout.magenta_code (), internal->opts.realtime ? "real" : "process",
       tout.normal_code ());

  SECTION ("glue usage");

  internal->print_tier_usage_statistics ();

#endif // ifndef QUIET
}

void Internal::print_resource_usage () {
#ifndef QUIET
  SECTION ("resources");
  uint64_t m = maximum_resident_set_size ();
  MSG ("total process time since initialization: %12.2f    seconds",
       internal->process_time ());
  MSG ("total real time since initialization:    %12.2f    seconds",
       internal->real_time ());
  MSG ("maximum resident set size of process:    %12.2f    MB",
       m / (double) (1l << 20));
#endif
}

/*------------------------------------------------------------------------*/

void Checker::print_stats () {

  if (!stats.added && !stats.deleted)
    return;

  SECTION ("checker statistics");

  MSG ("checks:          %15" PRId64 "", stats.checks);
  MSG ("assumptions:     %15" PRId64 "   %10.2f    per check",
       stats.assumptions, relative (stats.assumptions, stats.checks));
  MSG ("propagations:    %15" PRId64 "   %10.2f    per check",
       stats.propagations, relative (stats.propagations, stats.checks));
  MSG ("original:        %15" PRId64 "   %10.2f %%  of all clauses",
       stats.original, percent (stats.original, stats.added));
  MSG ("derived:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.derived, percent (stats.derived, stats.added));
  MSG ("deleted:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.deleted, percent (stats.deleted, stats.added));
  MSG ("insertions:      %15" PRId64 "   %10.2f %%  of all clauses",
       stats.insertions, percent (stats.insertions, stats.added));
  MSG ("collections:     %15" PRId64 "   %10.2f    deleted per collection",
       stats.collections, relative (stats.collections, stats.deleted));
  MSG ("collisions:      %15" PRId64 "   %10.2f    per search",
       stats.collisions, relative (stats.collisions, stats.searches));
  MSG ("searches:        %15" PRId64 "", stats.searches);
  MSG ("units:           %15" PRId64 "", stats.units);
}

void LratChecker::print_stats () {

  if (!stats.added && !stats.deleted)
    return;

  SECTION ("lrat checker statistics");

  MSG ("checks:          %15" PRId64 "", stats.checks);
  MSG ("insertions:      %15" PRId64 "   %10.2f %%  of all clauses",
       stats.insertions, percent (stats.insertions, stats.added));
  MSG ("original:        %15" PRId64 "   %10.2f %%  of all clauses",
       stats.original, percent (stats.original, stats.added));
  MSG ("derived:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.derived, percent (stats.derived, stats.added));
  MSG ("rat:             %15" PRId64 "   %10.2f %%  of derived clauses",
       stats.rat, percent (stats.rat, stats.derived));
  MSG ("deleted:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.deleted, percent (stats.deleted, stats.added));
  MSG ("finalized:       %15" PRId64 "   %10.2f %%  of all clauses",
       stats.finalized, percent (stats.finalized, stats.added));
  MSG ("collections:     %15" PRId64 "   %10.2f    deleted per collection",
       stats.collections, relative (stats.collections, stats.deleted));
  MSG ("collisions:      %15" PRId64 "   %10.2f    per search",
       stats.collisions, relative (stats.collisions, stats.searches));
  MSG ("searches:        %15" PRId64 "", stats.searches);
}

} // namespace CaDiCaL
