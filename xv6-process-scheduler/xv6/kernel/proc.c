#include "types.h"
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "pstat.h"

struct
{
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

struct queue
{
  struct proc *headNode;
  struct proc *endNode;
};

// Stores proc objects for each of the four priority levels
struct queue priorityQueue[4];

// Max allowed ticks for each level
int maxAllowedTicks[4] = {0, 32, 16, 8};

// Tracks the curent tick count for each priority level
int counter[4];

static struct proc * initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc *
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);
  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if (p->state == UNUSED)
      goto found;
  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  p->priority = 3;
  p->tickMarks[0] = 0;
  p->tickMarks[1] = 0;
  p->tickMarks[2] = 0;
  p->tickMarks[3] = 0;
  p->ticks[0] = 0;
  p->ticks[1] = 0;
  p->ticks[2] = 0;
  p->ticks[3] = 0;
  release(&ptable.lock);

  // Allocate kernel stack if possible.
  if ((p->kstack = kalloc()) == 0)
  {
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe *)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint *)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context *)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  // Initalize the priority queue and place the new proc at priority level 3
  if (priorityQueue[3].headNode == NULL && priorityQueue[3].endNode == NULL)
  {
    priorityQueue[3].endNode = p;
    priorityQueue[3].headNode = p;
  }
  else
  {
    priorityQueue[3].endNode->next = p;
    priorityQueue[3].endNode = p;
  }
  p->next = NULL;

  return p;
}

// Set up first user process.
void userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  acquire(&ptable.lock);
  initproc = p;
  if ((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0; // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;
  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int growproc(int n)
{
  uint sz;

  sz = proc->sz;
  if (n > 0)
  {
    if ((sz = allocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  else if (n < 0)
  {
    if ((sz = deallocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  proc->sz = sz;
  switchuvm(proc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int fork(void)
{
  int i, pid;
  struct proc *np;

  // Allocate process.
  if ((np = allocproc()) == 0)
    return -1;

  // Copy process state from p.
  if ((np->pgdir = copyuvm(proc->pgdir, proc->sz)) == 0)
  {
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = proc->sz;
  np->parent = proc;
  *np->tf = *proc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for (i = 0; i < NOFILE; i++)
    if (proc->ofile[i])
      np->ofile[i] = filedup(proc->ofile[i]);
  np->cwd = idup(proc->cwd);

  pid = np->pid;
  np->state = RUNNABLE;
  safestrcpy(np->name, proc->name, sizeof(proc->name));
  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void exit(void)
{
  struct proc *p;
  int fd;

  if (proc == initproc)
    panic("init exiting");

  // Close all open files.
  for (fd = 0; fd < NOFILE; fd++)
  {
    if (proc->ofile[fd])
    {
      fileclose(proc->ofile[fd]);
      proc->ofile[fd] = 0;
    }
  }

  iput(proc->cwd);
  proc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(proc->parent);

  // Pass abandoned children to init.
  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if (p->parent == proc)
    {
      p->parent = initproc;
      if (p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  proc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int wait(void)
{
  struct proc *p;
  int havekids, pid;

  acquire(&ptable.lock);
  for (;;)
  {
    // Scan through table looking for zombie children.
    havekids = 0;
    for (p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    {
      if (p->parent != proc)
        continue;
      havekids = 1;
      if (p->state == ZOMBIE)
      {
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->state = UNUSED;
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if (!havekids || proc->killed)
    {
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(proc, &ptable.lock); //DOC: wait-sleep
  }
}

/*
 Remove the proc from the specified priority queue

 @param int currentPriority specifies the priority level queue to remove the proc from
 @param proc p   The proc to remove from the queue
*/
int removeFromPriorityQueue(struct proc * previousNode, struct proc * curProc, int stat){
  int currentPriority = curProc->priority;

  if (priorityQueue[currentPriority].headNode == priorityQueue[currentPriority].endNode)
  {
    priorityQueue[currentPriority].headNode = NULL;
    priorityQueue[currentPriority].endNode = NULL;
    return 4; // break code
  }
  else if (priorityQueue[currentPriority].headNode == curProc)
  {
    priorityQueue[currentPriority].headNode = curProc->next;
    if(stat > 0){
    curProc = curProc->next;
    }
  }
  else
  {
    previousNode->next = curProc->next;
    if (priorityQueue[currentPriority].endNode == curProc)
    {
      priorityQueue[currentPriority].endNode = previousNode;
      return 4; //break code
    }
    if(stat > 0){
    curProc = curProc->next;
    }
  }
  return 0;
}

/*
Custom MLFW scheduler with four priority levels
*/
void scheduler(void)
{
  // Declare current and prev proc nodes
  struct proc * curProc;

  // Loop indefinietly 
  for (;;)
  {
    // Attempt to aquire a lock on the process table and enable CPU interrupts 
    sti();
    acquire(&ptable.lock);

    int priorityLevel;
    int currentPriority;
    for (priorityLevel = 0; priorityLevel < 4; ++priorityLevel)
    {
      struct proc * previousNode = NULL;
      for (curProc = priorityQueue[priorityLevel].headNode; curProc != NULL;)
      {

        // TODO: Fix bugs
        // // Calculate the current wait_ticks value
        // p->wait_ticks[priorityLevel] = counter[priorityLevel] - p->tickMarks[priorityLevel];
        // // Boost priority if process has waited over 500 ticks for P0 or more than 1x greater than the maxAllowedTicks for the current priority level
        // if (((p->wait_ticks[priorityLevel] > 500) && p->priority == 0) || (p->wait_ticks[priorityLevel] > (maxAllowedTicks[priorityLevel] * 10)))
        // {
        //   if (p->priority != 3)
        //   {
        //     p->priority++;
        //   }
        // }
        // counter[priorityLevel]++;

        if (curProc->state == RUNNABLE)
        {
          // TODO: Fix bugs
          // p->wait_ticks[priorityLevel] = 0;
          // p->tickMarks[priorityLevel] = counter[i];
          
          // Set the current proc state to running and invoke context switch
          
          
          proc = curProc;
          switchuvm(curProc);
          curProc->state = RUNNING;
          swtch(&cpu->scheduler, proc->context);
          switchkvm();
          currentPriority = curProc->priority;

          // Imcrement ticks and determine if the current proc should be removed from the current priority queue   
          if (++curProc->ticks[currentPriority] >= maxAllowedTicks[currentPriority] && currentPriority != 0)
          {
            if(removeFromPriorityQueue(previousNode, curProc, 0) == 4){
              //break;
            }

            // After removing the proc from the queue, lower the priority
            if (curProc->priority != 0)
            {         
              currentPriority = --curProc->priority;
            }

            // Append the proc to the end of the new priotiy queue or move to the back of the current queue
            if (priorityQueue[currentPriority].headNode == NULL &&
                priorityQueue[currentPriority].endNode == NULL)
            {
              priorityQueue[currentPriority].headNode = curProc;
              priorityQueue[currentPriority].endNode = curProc;
            }
            else
            { 
              priorityQueue[currentPriority].endNode->next = curProc;
              priorityQueue[currentPriority].endNode = curProc;
              
            }
            curProc->next = NULL;
          }

          // Reset the proc var and break after updating the queues
          proc = 0;
          priorityLevel = -1;
          break;
        }
        else if (curProc->state == UNUSED)
        {
          currentPriority = curProc->priority;
          if (removeFromPriorityQueue(previousNode, curProc, 1) == 4){
            break;
          }
        }
        else
        {
          // Otherwise, advance to the next proc in the queue and update the previousNode reference
          previousNode = curProc;
          curProc = curProc->next;
        }
      }
    }
    // Release the lock on the process table
    release(&ptable.lock);
  }
}

/*
Check process table flags and invoke kernel panic as necessary
*/
void checkProcessTableFlags(void)
{
  if (readeflags() & FL_IF)
  {
    panic("sched interruptible");
  }
  if (cpu->ncli != 1)
  {
    panic("sched locks");
  }
  if (proc->state == RUNNING)
  {
    panic("sched running");
  }
    if (!holding(&ptable.lock))
  {
    panic("sched ptable.lock");
  }
}

/*
Entry pointer for the MLFQ scheduler 
*/
void sched(void)
{
  checkProcessTableFlags();
  // Fetch the current CPI intena value
  int cpuValue = cpu->intena;

  // Initiate a context switch and invoke the schuduler
  swtch(&proc->context, cpu->scheduler);

  // Set the new CPI intena value
  cpu->intena = cpuValue;
}

// Give up the CPU for one scheduling round.
void yield(void)
{
  acquire(&ptable.lock); //DOC: yieldlock
  proc->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void forkret(void)
{
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void sleep(void *chan, struct spinlock *lk)
{
  if (proc == 0)
    panic("sleep");

  if (lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if (lk != &ptable.lock)
  {                        //DOC: sleeplock0
    acquire(&ptable.lock); //DOC: sleeplock1
    release(lk);
  }

  // Go to sleep.
  proc->chan = chan;
  proc->state = SLEEPING;
  sched();

  // Tidy up.
  proc->chan = 0;

  // Reacquire original lock.
  if (lk != &ptable.lock)
  { //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if (p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if (p->pid == pid)
    {
      p->killed = 1;
      // Wake process from sleep if necessary.
      if (p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void procdump(void)
{
  static char *states[] = {
          [UNUSED] "unused",
          [EMBRYO] "embryo",
          [SLEEPING] "sleep ",
          [RUNNABLE] "runble",
          [RUNNING] "run   ",
          [ZOMBIE] "zombie"};
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for (p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if (p->state == UNUSED)
      continue;
    if (p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if (p->state == SLEEPING)
    {
      getcallerpcs((uint *)p->context->ebp + 2, pc);
      for (i = 0; i < 10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

/*
Passes a psat object to pinfo to fetch basic info about a process
including inuse status, priority level, pid, process state and ticks. 

@returns int status representing the sucuess code
@param pstat output param to store the proc info
*/
int getpinfo(struct pstat *procOutParam)
{
  // Attempt to aquire a lock on the process table
  acquire(&ptable.lock);

  // Iterate through each process in the process table and check the status
  int i = 0;
  while (i < NPROC)
  {
    // Set the inuse flag depending on the process state
    if (ptable.proc[i].state == RUNNING || ptable.proc[i].state == SLEEPING)
    {
      procOutParam->inuse[i] = 1;
    }
    else
    {
      procOutParam->inuse[i] = 0;
    }

    // Save the process info to the pstat output param
    procOutParam->pid[i] = ptable.proc[i].pid;
    procOutParam->priority[i] = ptable.proc[i].priority;

    // Populate ticks at each of the four priorties
    int j = 0;
    while (j < 4)
    {
      procOutParam->ticks[i][j] = ptable.proc[i].ticks[j];
      j++;
    }
    i++;
  }

  // Release the lock on the process table before returning a sucuess status
  release(&ptable.lock);
  return 0;
}
