#ifndef _features_hpp_INCLUDED
#define _features_hpp_INCLUDED

// Here we collect compile time configuration options using feature tests.

// This is only working for Linux.

extern "C" {
#include <features.h>
};


// According to the man page of 'putc_unlocked' this is its feature test.

#if _POSIX_C_SOURCE >= 1 || defined(_XOPEN_SOURCE) || defined(_POSIX_SOURCE) || defined(_BSD_SOURCE) || defined(_SVID_SOURCE)
#define HAVE_UNLOCKED_IO
#endif

#endif
