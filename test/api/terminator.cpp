#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <atomic>
#include <chrono>
#include <thread>

static int n = 11;

static int ph (int p, int h) {
  assert (0 <= p), assert (p < n + 1);
  assert (0 <= h), assert (h < n);
  return 1 + h * (n + 1) + p;
}

struct Terminator : public CaDiCaL::Terminator {
  Terminator (): terminate_requested (false) { }

  bool terminate () override {
    return terminate_requested.load (std::memory_order_acquire);
  }

  void notify_terminate () {
    terminate_requested.store (true, std::memory_order_release);
  }

  void reset_terminate () {
    terminate_requested.store (false, std::memory_order_release);
  }
private:
  std::atomic<bool> terminate_requested;
};

static CaDiCaL::Solver solver;
static Terminator terminator;

int main () {
  solver.set ("factor", 0);
  solver.connect_terminator (&terminator);
  terminator.reset_terminate ();

  // Construct a pigeon hole formula for 'n+1' pigeons in 'n' holes.
  //
  for (int h = 0; h < n; h++)
    for (int p1 = 0; p1 < n + 1; p1++)
      for (int p2 = p1 + 1; p2 < n + 1; p2++)
        solver.add (-ph (p1, h)), solver.add (-ph (p2, h)), solver.add (0);

  for (int p = 0; p < n + 1; p++) {
    for (int h = 0; h < n; h++)
      solver.add (ph (p, h));
    solver.add (0);
  }

  std::thread terminator_thread ([]() -> void {
    std::this_thread::sleep_for (std::chrono::milliseconds (100));
    terminator.notify_terminate ();
  });
  int res = solver.solve ();
  assert (!res);
  solver.statistics ();
  if (terminator_thread.joinable ())
    terminator_thread.join ();

  return 0;
}
