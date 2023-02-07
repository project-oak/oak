/*
 * File: cancel2.c
 *
 * Test Synopsis: Test SEH or C++ cancel exception handling within
 * application exception blocks.
 *
 * Test Method (Validation or Falsification):
 * - 
 *
 * Requirements Tested:
 * -
 *
 * Features Tested:
 * - 
 *
 * Cases Tested:
 * - 
 *
 * Description:
 * - 
 *
 * Environment:
 * - 
 *
 * Input:
 * - None.
 *
 * Output:
 * - File name, Line number, and failed expression on failure.
 * - No output on success.
 *
 * Assumptions:
 * - have working pthread_create, pthread_self, pthread_mutex_lock/unlock
 *   pthread_testcancel, pthread_cancel, pthread_join
 *
 * Pass Criteria:
 * - Process returns zero exit status.
 *
 * Fail Criteria:
 * - Process returns non-zero exit status.
 */

#include "test.h"

/*
 * Create NUMTHREADS threads in addition to the Main thread.
 */
enum {
  NUMTHREADS = 10
};

typedef struct bag_t_ bag_t;
struct bag_t_ {
  int threadnum;
  int started;
  /* Add more per-thread state variables here */
};

static bag_t threadbag[NUMTHREADS + 1];

static pthread_mutex_t waitLock = PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP;

void *
mythread(void * arg)
{
  int result = 0;
  bag_t * bag = (bag_t *) arg;

  assert(bag == &threadbag[bag->threadnum]);
  assert(bag->started == 0);
  bag->started = 1;

  /* Set to known state and type */

  assert(pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL) == 0);

  switch (bag->threadnum % 2)
    {
    case 0:
      assert(pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL) == 0);
      result = 0;
      break;
    case 1:
      assert(pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, NULL) == 0);
      result = 1;
      break;
    }

  /* Wait for go from main */
  assert(pthread_mutex_lock(&waitLock) == 0);
  assert(pthread_mutex_unlock(&waitLock) == 0);
  sched_yield();

  for (;;)
    {	  
      pthread_testcancel();
    }

  return (void *) (size_t)result;
}

int
main()
{
  int failed = 0;
  int i;
  pthread_t t[NUMTHREADS + 1];

  assert((t[0] = pthread_self()) != NULL);
  assert(pthread_mutex_lock(&waitLock) == 0);

  for (i = 1; i <= NUMTHREADS; i++)
    {
      threadbag[i].started = 0;
      threadbag[i].threadnum = i;
      assert(pthread_create(&t[i], NULL, mythread, (void *) &threadbag[i]) == 0);
    }

  /*
   * Code to control or munipulate child threads should probably go here.
   */
  Sleep(500);

  assert(pthread_mutex_unlock(&waitLock) == 0);

  Sleep(500);

  for (i = 1; i <= NUMTHREADS; i++)
    {
      assert(pthread_cancel(t[i]) == 0);
    }

  /*
   * Give threads time to run.
   */
  Sleep(NUMTHREADS * 100);

  /*
   * Standard check that all threads started.
   */
  for (i = 1; i <= NUMTHREADS; i++)
    { 
      if (!threadbag[i].started)
	{
	  failed |= !threadbag[i].started;
	  fprintf(stderr, "Thread %d: started %d\n", i, threadbag[i].started);
	}
    }

  assert(!failed);

  /*
   * Check any results here. Set "failed" and only print output on failure.
   */
  failed = 0;
  for (i = 1; i <= NUMTHREADS; i++)
    {
      int fail = 0;
      void *result = 0;

      assert(pthread_join(t[i], &result) == 0);
      fail = (result != PTHREAD_CANCELED);
      if (fail)
	{
	  fprintf(stderr, "Thread %d: started %d: location %d: cancel type %s\n",
		  i,
		  threadbag[i].started,
		  result,
		  (((int)(size_t)result % 2) == 0) ? "ASYNCHRONOUS" : "DEFERRED");
	}
      failed |= fail;
    }

  assert(!failed);

  /*
   * Success.
   */
  return 0;
}

