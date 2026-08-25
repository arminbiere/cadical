
#include "internal.hpp"

namespace CaDiCaL {
#ifndef QUIET

// Initialize all profile counters with constant name and profiling level.

Profiles::Profiles (Internal *s)
    : internal (s)
#define PROFILE(NAME, LEVEL) , NAME (#NAME, LEVEL)
          PROFILES
#undef PROFILE
{
}

void Internal::start_profiling (Profile &profile, double s,
                                int64_t s_ticks) {
  LOG ("START PROFILE[%s]", profile.name);
  assert (profile.level <= opts.profile);
  assert (!profile.active);
  profile.started = s;
  profile.started_ticks = s_ticks;
  profile.active = true;
}

void Internal::stop_profiling (Profile &profile, double s,
                               int64_t s_ticks) {
  LOG ("STOP PROFILE[%s]", profile.name);
  assert (profile.level <= opts.profile);
  assert (profile.active);
  assert (profile.started_ticks <= s_ticks);
  profile.value += s - profile.started;
  profile.search_ticks += s_ticks - profile.started_ticks;
  profile.active = false;
}

double Internal::update_profiles () {
  double now = time ();
#define PROFILE(NAME, LEVEL) \
  do { \
    Profile &profile = profiles.NAME; \
    if (profile.active) { \
      assert (profile.level <= opts.profile); \
      profile.value += now - profile.started; \
      profile.started = now; \
    } \
  } while (0);
  PROFILES
#undef PROFILE
  return now;
}

double Internal::solve_time () {
  (void) update_profiles ();
  return profiles.solve.value;
}

#define PRT(S, T) \
  MSG ("%s" S "%s", tout.magenta_code (), T, tout.normal_code ())

void Internal::print_profile () {
  double now = update_profiles ();
  const char *time_type = opts.realtime ? "real" : "process";
  SECTION ("run-time profiling");
  PRT ("%s time and ticks taken by individual solving procedures",
       time_type);
  PRT ("(percentage relative to %s time for solving)", time_type);
  LINE ();
  const size_t size = sizeof profiles / sizeof (Profile);
  struct Profile *profs[size];
  size_t n = 0;
#define PROFILE(NAME, LEVEL) \
  do { \
    if (LEVEL > opts.profile) \
      break; \
    Profile *p = &profiles.NAME; \
    if (p == &profiles.solve) \
      break; \
    if (!profiles.NAME.value && p != &profiles.parse && \
        p != &profiles.search && p != &profiles.simplify) \
      break; \
    profs[n++] = p; \
  } while (0);
  PROFILES
#undef PROFILE

  assert (n <= size);

  // Explicit bubble sort to avoid heap allocation since 'print_profile'
  // is also called during catching a signal after out of heap memory.
  // This only makes sense if 'profs' is allocated on the stack, and
  // not the heap, which should be the case.

  double solve = profiles.solve.value;
  uint64_t solve_ticks = profiles.solve.search_ticks;

  for (size_t i = 0; i < n; i++) {
    for (size_t j = i + 1; j < n; j++)
      if (profs[j]->value > profs[i]->value)
        swap (profs[i], profs[j]);
    MSG ("%12.2f %7.2f%% %-20s %12" PRId64 " %7.2f%%", profs[i]->value,
         percent (profs[i]->value, solve), profs[i]->name,
         profs[i]->search_ticks,
         percent (profs[i]->search_ticks, solve_ticks));
  }

  MSG ("  "
       "==================================================================="
       "=");
  MSG ("%12.2f %7.2f%% %-20s %12" PRId64 " %7.2f%%", solve,
       percent (solve, now), "solve", solve_ticks, 100.0);

  LINE ();
  PRT ("last line shows %s time for solving", time_type);
  PRT ("(percentage relative to total %s time)", time_type);
}

/*------------------------------------------------------------------------*/

// C++ 11 version of std::make_index_sequence<N>
template <std::size_t N, std::size_t... Is>
struct make_indices : make_indices<N - 1, N - 1, Is...> {};

template <std::size_t... Is> struct make_indices<0, Is...> {
  typedef ProfileIndices<Is...> type;
};

template <typename... Profiles>
ProfileContext<Profiles...>::ProfileContext (Internal *internal,
                                             Profiles... profiles)
    : internal (internal), profiles (profiles...) {
  enterContext ();
}

template <typename... Profiles>
ProfileContext<Profiles...>::~ProfileContext () {
  leaveContext ();
}

template <typename... Profiles>
void ProfileContext<Profiles...>::enterContext () {
  enterContext (typename make_indices<sizeof...(Profiles)>::type{});
}

template <typename... Profiles>
void ProfileContext<Profiles...>::leaveContext () {
  leaveContext (typename make_indices<sizeof...(Profiles)>::type{});
}

template <typename... Profiles>
template <size_t... Is>
void ProfileContext<Profiles...>::enterContext (
    ProfileIndices<Is...> indices) {
  (void) indices;

  const double time = internal->time ();
  const int64_t ticks = internal->stats.ticks;
  const int level = internal->opts.profile;

  using expand = int[];
  (void) expand{
      (std::get<Is> (profiles).enterContext (internal, time, ticks, level),
       0)...};
}

template <typename... Profiles>
template <size_t... Is>
void ProfileContext<Profiles...>::leaveContext (
    ProfileIndices<Is...> indices) {
  (void) indices;

  const double time = internal->time ();
  const int64_t ticks = internal->stats.ticks;
  const int level = internal->opts.profile;

  using expand = int[];
  (void) expand{
      (std::get<Is> (profiles).leaveContext (internal, time, ticks, level),
       0)...};
}

// Explicit instantiations as Internal is now available
template class ProfileContext<ResumeProfile>;
template class ProfileContext<ResumeProfile, ResumeProfile>;
template class ProfileContext<ResumeProfile, ResumeProfile, ResumeProfile>;
template class ProfileContext<ResumeProfile, PauseProfile>;
template class ProfileContext<ResumeProfile, PauseProfile, PauseProfile>;
template class ProfileContext<PauseProfile, PauseProfile>;
template class ProfileContext<ResumeProfile, ResumeProfile, PauseProfile,
                              PauseProfile, PauseProfile>;

void ResumeProfile::enterContext (Internal *internal, double time,
                                  int64_t ticks, int level) {
  entered = condition && !profile.active && profile.level <= level;
  if (entered)
    internal->start_profiling (profile, time, ticks);
}

void ResumeProfile::leaveContext (Internal *internal, double time,
                                  int64_t ticks, int level) {
  (void) level;
  if (entered && profile.active)
    internal->stop_profiling (profile, time, ticks);
}

void PauseProfile::enterContext (Internal *internal, double time,
                                 int64_t ticks, int level) {
  (void) level;
  entered = condition && profile.active;
  if (entered)
    internal->stop_profiling (profile, time, ticks);
}

void PauseProfile::leaveContext (Internal *internal, double time,
                                 int64_t ticks, int level) {
  (void) level;
  if (entered && !profile.active)
    internal->start_profiling (profile, time, ticks);
}

#endif // ifndef QUIET

ModeResumeContext::ModeResumeContext (Internal *internal, int mode)
    : internal (internal), mode (mode), entered (false) {
  enterContext ();
}

ModeResumeContext::~ModeResumeContext () { leaveContext (); }

void ModeResumeContext::enterContext () {
  entered = !internal->in_mode (static_cast<Internal::Mode> (mode));
  if (entered)
    internal->set_mode (static_cast<Internal::Mode> (mode));
}

void ModeResumeContext::leaveContext () {
  if (entered)
    internal->reset_mode (static_cast<Internal::Mode> (mode));
  entered = !entered;
}

ModePauseContext::ModePauseContext (Internal *internal, int mode)
    : internal (internal), mode (mode), entered (false) {
  enterContext ();
}

ModePauseContext::~ModePauseContext () { leaveContext (); }

void ModePauseContext::enterContext () {
  entered = internal->in_mode (static_cast<Internal::Mode> (mode));
  if (entered)
    internal->reset_mode (static_cast<Internal::Mode> (mode));
}

void ModePauseContext::leaveContext () {
  if (entered)
    internal->set_mode (static_cast<Internal::Mode> (mode));
  entered = !entered;
}

} // namespace CaDiCaL
