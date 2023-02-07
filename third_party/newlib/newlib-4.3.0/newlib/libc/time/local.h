/* local header used by libc/time routines */
#include <_ansi.h>
#include <time.h>
#include <sys/_tz_structs.h>

#define SECSPERMIN	60L
#define MINSPERHOUR	60L
#define HOURSPERDAY	24L
#define SECSPERHOUR	(SECSPERMIN * MINSPERHOUR)
#define SECSPERDAY	(SECSPERHOUR * HOURSPERDAY)
#define DAYSPERWEEK	7
#define MONSPERYEAR	12

#define YEAR_BASE	1900
#define EPOCH_YEAR      1970
#define EPOCH_WDAY      4
#define EPOCH_YEARS_SINCE_LEAP 2
#define EPOCH_YEARS_SINCE_CENTURY 70
#define EPOCH_YEARS_SINCE_LEAP_CENTURY 370

#define isleap(y) ((((y) % 4) == 0 && ((y) % 100) != 0) || ((y) % 400) == 0)

int         __tzcalc_limits (int __year);

extern const int __month_lengths[2][MONSPERYEAR];

void _tzset_unlocked_r (struct _reent *);
void _tzset_unlocked (void);

/* locks for multi-threading */
#ifdef __SINGLE_THREAD__
#define TZ_LOCK
#define TZ_UNLOCK
#else
#define TZ_LOCK __tz_lock()
#define TZ_UNLOCK __tz_unlock()
#endif

void __tz_lock (void);
void __tz_unlock (void);

