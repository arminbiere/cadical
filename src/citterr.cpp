#include <new>

extern "C" {
void citten_error (const char *, ...) { throw std::bad_alloc (); }
}
