#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

/*------------------------------------------------------------------------*/

// Macros for compact message code.

#ifndef QUIET

#define MSG(...) internal->message (__VA_ARGS__)
#define PHASE(...) internal->phase (__VA_ARGS__)
#define SECTION(...) internal->section (__VA_ARGS__)
#define VERBOSE(...) internal->verbose (__VA_ARGS__)

#else

#define MSG(...) do { } while (0)
#define PHASE(...) do { } while (0)
#define SECTION(...) do { } while (0)
#define VERBOSE(...) do { } while (0)

#endif

#define FATAL internal->fatal
#define WARNING(...) internal->warning (__VA_ARGS__)

/*------------------------------------------------------------------------*/

#endif // ifndef _message_h_INCLUDED
