#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "devices/timer.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* Number of digits after the decimal for fixed point numbers */
#define FP_DEC 16
/* Fixed point conversion factor */
#define FP_F (1 << FP_DEC)

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

/* Array of lists used to implement the ready queue in 
   MLFQS. */
static struct list ready_mlfqs[PRI_MAX+1];

/* The priority of the highest non-empty queue in mlfqs scheduling. */
static int mlfqs_highest = PRI_MIN-1;

/* List of threads in THREAD_BLOCKED state that are waiting
   till the tick count specified in their struct thread -> wakeup 
   (The list is maintained in ascending order of wakeup time) */
static struct list wait_list;

/* List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Thread to update load_avg, recent_cpu and priorities every second. */
static struct thread *update_thread;

/* Wakeup thread */
static struct thread *wakeup_thread;

/* Next wakeup time */
static int64_t next_wakeup;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame 
  {
    void *eip;                  /* Return address. */
    thread_func *function;      /* Function to call. */
    void *aux;                  /* Auxiliary data for function. */
  };

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */

/* Average system load */
static int64_t load_avg;

/* Constants */
static const int64_t LFRAC = ((int64_t)59*FP_F/60);
static const int64_t RFRAC = (FP_F/(int64_t)60);

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static void wakeup(void * nullptr);
static void update (void * nullptr);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *) UNUSED;
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);
void thread_schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) 
{
  ASSERT (intr_get_level () == INTR_OFF);

  lock_init (&tid_lock);
  if(thread_mlfqs) {
    int i;
    for(i=0; i<=PRI_MAX; i++) {
      list_init (ready_mlfqs+i);
    }
  } else {
    list_init (&ready_list);
  }
  list_init (&ready_list);
  list_init (&wait_list);
  list_init (&all_list);

  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread ();
  init_thread (initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid ();
  initial_thread->recent_cpu = 0;
  initial_thread->nice = 0;
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) 
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init (&idle_started, 0);
  thread_create ("idle", PRI_MIN, idle, &idle_started);

  /* Create the wakeup thread */
  thread_create ("wakeup", PRI_MAX, wakeup, NULL);

  /* Create the update thread */
  thread_create ("update", PRI_MAX, update, NULL);

  /* Start preemptive thread scheduling. */
  intr_enable ();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down (&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (int64_t ticks) 
{
  struct thread *t = thread_current ();

  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;

  /* Unblocks the wakeup thread if sleeping threads need to be
    woken up. */
  if( (wakeup_thread->status == THREAD_BLOCKED) && (!list_empty(&wait_list))
      && (ticks >= next_wakeup) ) {
    thread_unblock(wakeup_thread);
    intr_yield_on_return ();
  }

  /* Update recent_cpu for the current running thread. */
  if(t!=idle_thread) {
    (t->recent_cpu)+=FP_F;
  }

  /* Wake the update thread up every second. */
  if (ticks%TIMER_FREQ==0) {
    if(update_thread->status == THREAD_BLOCKED) {
      thread_update_load_avg();
      thread_unblock(update_thread);
      intr_yield_on_return();
    }
  }

  /* Update thread priority value every fourth tick. */
  if (ticks%4==0) {
    thread_update_priority(t, NULL);
  }

  if(t!=wakeup_thread && t!=update_thread) {
    /* Pre-empt the running thread if it is no longer the highest priority. */
    check_preempt(true);
    /* Enforce preemption on expiry of time slice. */
    if (++thread_ticks >= TIME_SLICE)
      intr_yield_on_return ();
  }
}

/* Prints thread statistics. */
void
thread_print_stats (void) 
{
  printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
          idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux) 
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;
  enum intr_level old_level;

  ASSERT (function != NULL);

  /* Allocate thread. */
  t = palloc_get_page (PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread (t, name, priority);
  tid = t->tid = allocate_tid ();
  t->recent_cpu = thread_current()->recent_cpu;
  t->nice = thread_current()->nice;

  /* Ignore set priority in mlfqs mode, barring highest 
     priority threads. */
  if(thread_mlfqs && priority!=PRI_MAX) {
    thread_update_priority(t, NULL);
  }
  
  /* Prepare thread for first run by initializing its stack.
     Do this atomically so intermediate values for the 'stack' 
     member cannot be observed. */
  old_level = intr_disable ();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame (t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame (t, sizeof *ef);
  ef->eip = (void (*) (void)) kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame (t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;

  intr_set_level (old_level);

  /* Add to run queue. */
  thread_unblock (t);

  /* If the new thread is higher priority than the 
     creator, preempt immediately. */
  check_preempt(false);
  return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) 
{
  ASSERT (!intr_context ());
  ASSERT (intr_get_level () == INTR_OFF);

  thread_current ()->status = THREAD_BLOCKED;
  schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) 
{
  enum intr_level old_level;

  ASSERT (is_thread (t));

  old_level = intr_disable ();
  ASSERT (t->status == THREAD_BLOCKED);
  ready_insert(t);
  t->status = THREAD_READY;
  intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void) 
{
  return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) 
{
  struct thread *t = running_thread ();
  
  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT (is_thread (t));
  ASSERT (t->status == THREAD_RUNNING);

  return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) 
{
  return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) 
{
  ASSERT (!intr_context ());

#ifdef USERPROG
  process_exit ();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it calls thread_schedule_tail(). */
  intr_disable ();
  list_remove (&thread_current()->allelem);
  thread_current ()->status = THREAD_DYING;
  schedule ();
  NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  if (cur != idle_thread) 
    ready_insert(cur);
  cur->status = THREAD_READY;
  schedule ();
  intr_set_level (old_level);
}

/* Check if a higher priority thread is in the ready queue and
   preempt the current thread if necessary. */
void
check_preempt(bool ext_interrupt)
{
  struct thread* t = thread_current();
  if(t==wakeup_thread || t==update_thread)
    return;

  if(thread_mlfqs) {
    if(mlfqs_highest > t->priority) {
      if(ext_interrupt)
        intr_yield_on_return();
      else 
        thread_yield();
    }
  } else {
    if(!list_empty(&ready_list)) {
      struct thread* ready_head = list_entry(list_begin(&ready_list), struct thread, elem);
      if(ready_head->priority > t->priority) {
        if(ext_interrupt)
          intr_yield_on_return();
        else 
          thread_yield();
      }
    }
  }
}

/* Function used by the wakeup thread to wake threads 
   in the waitlist, and then block itself till the next
   time it needs to run. */
void
wakeup(void * nullptr UNUSED) 
{
  wakeup_thread = thread_current();
  while(1) {
    int64_t ticks = timer_ticks();
    thread_wakeup(ticks);
    enum intr_level old_level = intr_disable();
    wakeup_thread->status = THREAD_BLOCKED;
    schedule();
    intr_set_level(old_level);
  }
}

/* Function to wake threads up from the wait list */
void
thread_wakeup(int64_t ticks) {
  struct list_elem* e;
  if(!list_empty(&wait_list)) {
    e = list_begin(&wait_list);
    while(e!=list_end(&wait_list)) {
      struct thread * curthread = list_entry(e, struct thread, elem);
      if(ticks >= curthread->wakeup) {
        struct list_elem* next = list_remove(e);
        ready_insert(curthread);
        curthread->wakeup=0;
        curthread->status=THREAD_READY;
        e = next;
        continue;
      } else {
        next_wakeup = curthread->wakeup;
        break;
      }
    }
  } else {
    next_wakeup=0;
  }
}

/* Function to change the state of the current thread to
   THREAD_BLOCKED, and place it on the wait list. */
void
thread_sleep(int64_t sleep_ticks) {
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  if (cur != idle_thread) {
    cur->wakeup = sleep_ticks + timer_ticks(); 
    list_insert_ordered(&wait_list, &cur->elem, wakeup_lower, NULL);
    //update next wakeup if necessary
    if(&cur->elem==list_begin(&wait_list)) {
      next_wakeup = cur->wakeup;
    }
    cur->status = THREAD_BLOCKED;
  }
  schedule();
  intr_set_level (old_level);
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT (intr_get_level () == INTR_OFF);

  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      func (t, aux);
    }
}

/* Function executed by the update thread to update recent_cpu and 
   priority values for all threads, and then block itself. */
void update (void * nullptr UNUSED) {
  update_thread = thread_current();
  while (1)
  {
    struct list_elem *e;
    for (e = list_begin (&all_list); e != list_end (&all_list);
         e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      thread_update_recent_cpu(t, NULL);
      thread_update_priority(t, NULL);
    }
    if(thread_mlfqs)
      mlfqs_update_highest();
    enum intr_level old_level = intr_disable();
    update_thread->status = THREAD_BLOCKED;
    schedule();
    intr_set_level(old_level);
  }
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void
thread_set_priority (int new_priority) 
{
  enum intr_level old_level = intr_disable();
  if(!thread_mlfqs) {
    struct thread* t = thread_current();
    t->priority = new_priority;
    intr_set_level(old_level);
    //yield if a higher priority thread is in the ready queue.
    check_preempt(false);
  }
}

/* Returns the current thread's priority. */
int
thread_get_priority (void) 
{
  return thread_current()->priority;
}

/* Function to update the priority value of a thread. */
void
thread_update_priority (struct thread* t, void* initial_nice)
{
  //check if priority update is due to nice value change of the initial thread
  if(initial_nice!=NULL) {
    int new_priority = roundoff_priority(PRI_MAX - 2*t->nice);
    if(t->priority!=new_priority) {
      t->priority = new_priority;
      rearrange(t);
    }
  } else if(t!=idle_thread && t!=wakeup_thread && t!=update_thread && t!=initial_thread) {
    int64_t new_priority_fp = ((int64_t)PRI_MAX)*FP_F - (t->recent_cpu/4) - (((int64_t)2)*t->nice*FP_F);
    int new_priority = roundoff_priority(get_rounded_integer(new_priority_fp));
    if(t->priority!=new_priority) {
      t->priority = new_priority;
      rearrange(t);
    }
  }
}

/* Rounds off the priority value to keep it in
   range, if necessary. */
int
roundoff_priority(int priority) {
  if(priority<PRI_MIN) {
    return PRI_MIN;
  } else if(priority>PRI_MAX) {
    return PRI_MAX;
  } else {
    return priority;
  }
}

/* Repositions the element in the ready queue 
   upon change in priority. */
void 
rearrange(struct thread* t) {
  if(t->status == THREAD_READY) {
    list_remove(&t->elem);
    ready_insert(t);
  }
}

/* Sets the current thread's nice value to NICE. */
void
thread_set_nice (int nice) 
{
  enum intr_level old_level = intr_disable();
  struct thread* t = thread_current();
  //adjust nice value to lie in range
  if(nice>20) {
    t->nice = 20;
  } else if(nice<-20) {
    t->nice = -20;
  } else {
    t->nice = nice;
  }
  thread_update_priority(t, t==initial_thread?t:NULL);
  intr_set_level(old_level);
  check_preempt(false);
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) 
{
  return thread_current()->nice;
}

/* Returns 100 times the system load average. */
int
thread_get_load_avg (void) 
{
  return get_rounded_integer(100*load_avg);
}

/* Calculates and updates load_avg. */
void
thread_update_load_avg (void) 
{
  int64_t ready_threads;
  if(thread_mlfqs) {
    ready_threads = (thread_current()!=idle_thread)?1:0;
    int i;
    for(i=0; i<=PRI_MAX; i++) {
      ready_threads += list_size(ready_mlfqs+i);
    }
  } else {
    ready_threads = list_size(&ready_list) + ((thread_current()!=idle_thread)?1:0);
  }
  load_avg = ((load_avg*LFRAC) >> FP_DEC ) + (ready_threads)*RFRAC;
}

/* Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) 
{
  struct thread* t = thread_current();
  return get_rounded_integer(100*t->recent_cpu);
}

/* Calculate and update recent_cpu value for a thread. */
void
thread_update_recent_cpu (struct thread* t, void* nullptr UNUSED) {
  int64_t load_frac = (2*load_avg*(FP_F))/(2*load_avg+FP_F);
  t->recent_cpu = load_frac*t->recent_cpu/(FP_F) + (int64_t)t->nice*FP_F;
}

/* Convert a fixed point number to the nearest rounded integer. */
int
get_rounded_integer(int64_t fixedpoint) {
    if(fixedpoint>=0) {
    fixedpoint += (1 << (FP_DEC-1));
  } else {
    fixedpoint -= (1 << (FP_DEC-1));
  }
  return fixedpoint/(FP_F);
}

/* Compare the priorities of two threads */
bool
priority_higher(const struct list_elem* a, const struct list_elem* b, void* aux UNUSED) {
  struct thread* t1 = list_entry(a, struct thread, elem);
  struct thread* t2 = list_entry(b, struct thread, elem);
  if(t1->priority > t2->priority)
    return true;
  else
    return false;
}

/* Compare the wakeup times of two threads */
bool
wakeup_lower(const struct list_elem* a, const struct list_elem* b, void* aux UNUSED) {
  struct thread* t1 = list_entry(a, struct thread, elem);
  struct thread* t2 = list_entry(b, struct thread, elem);
  if(t1->wakeup < t2->wakeup)
    return true;
  else
    return false;
}

/* Update the highest active queue in mlfqs */
void
mlfqs_update_highest(void) {
  ASSERT(thread_mlfqs);
  int i=PRI_MAX;
  while(i>=PRI_MIN && list_empty(ready_mlfqs+i)) {
    i--;
  }
  mlfqs_highest = i;
}

/* Insert a thread into the ready queue. */
void
ready_insert(struct thread* t) {
  if(thread_mlfqs) {
    list_push_back(ready_mlfqs+t->priority, &t->elem);
    if(mlfqs_highest < t->priority)
      mlfqs_highest = t->priority;
  } else {
    list_insert_ordered(&ready_list, &t->elem, priority_higher, NULL);
  }
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) 
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current ();
  sema_up (idle_started);

  for (;;) 
    {
      /* Let someone else run. */
      intr_disable ();
      thread_block ();

      /* Re-enable interrupts and wait for the next one.

         The `sti' instruction disables interrupts until the
         completion of the next instruction, so these two
         instructions are executed atomically.  This atomicity is
         important; otherwise, an interrupt could be handled
         between re-enabling interrupts and waiting for the next
         one to occur, wasting as much as one clock tick worth of
         time.

         See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
         7.11.1 "HLT Instruction". */
      asm volatile ("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) 
{
  ASSERT (function != NULL);

  intr_enable ();       /* The scheduler runs with interrupts off. */
  function (aux);       /* Execute the thread function. */
  thread_exit ();       /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread (void) 
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm ("mov %%esp, %0" : "=g" (esp));
  return pg_round_down (esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority)
{
  ASSERT (t != NULL);
  ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT (name != NULL);

  memset (t, 0, sizeof *t);
  t->status = THREAD_BLOCKED;
  strlcpy (t->name, name, sizeof t->name);
  t->stack = (uint8_t *) t + PGSIZE;
  t->priority = priority;
  t->wakeup=0;
  t->magic = THREAD_MAGIC;
  list_push_back (&all_list, &t->allelem);
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame (struct thread *t, size_t size) 
{
  /* Stack data is always allocated in word-size units. */
  ASSERT (is_thread (t));
  ASSERT (size % sizeof (uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) 
{
  if(thread_mlfqs) {
    if(mlfqs_highest<PRI_MIN) {
      return idle_thread;
    } else {
      struct thread* next = list_entry (list_pop_front (ready_mlfqs+mlfqs_highest), struct thread, elem);
      if(list_empty(ready_mlfqs+mlfqs_highest))
        mlfqs_update_highest();
      return next;
    }
  } else {
      if (list_empty (&ready_list))
      return idle_thread;
    else
      return list_entry (list_pop_front (&ready_list), struct thread, elem);
  }
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
thread_schedule_tail (struct thread *prev)
{
  struct thread *cur = running_thread ();
  
  ASSERT (intr_get_level () == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate ();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread) 
    {
      ASSERT (prev != cur);
      palloc_free_page (prev);
    }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until thread_schedule_tail()
   has completed. */
static void
schedule (void) 
{
  struct thread *cur = running_thread ();
  struct thread *next = next_thread_to_run ();
  struct thread *prev = NULL;

  ASSERT (intr_get_level () == INTR_OFF);
  ASSERT (cur->status != THREAD_RUNNING);
  ASSERT (is_thread (next));

  if (cur != next)
    prev = switch_threads (cur, next);
  thread_schedule_tail (prev);
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) 
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire (&tid_lock);
  tid = next_tid++;
  lock_release (&tid_lock);

  return tid;
}

/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);
