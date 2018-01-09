#include "types.h"
#include "x86.h"
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "proc.h"
#include "sysfunc.h"

int
sys_fork(void)
{
  return fork();
}

int
sys_exit(void)
{
  exit();
  return 0;  // not reached
}

int
sys_wait(void)
{
  return wait();
}

int
sys_kill(void)
{
  int pid;

  if(argint(0, &pid) < 0)
    return -1;
  return kill(pid);
}

int
sys_getpid(void)
{
  return proc->pid;
}

int
sys_sbrk(void)
{
  int addr;
  int n;

  if(argint(0, &n) < 0)
    return -1;
  addr = proc->sz;
  if(growproc(n) < 0)
    return -1;
  return addr;
}

int
sys_sleep(void)
{
  int n;
  uint ticks0;
  
  if(argint(0, &n) < 0)
    return -1;
  acquire(&tickslock);
  ticks0 = ticks;
  while(ticks - ticks0 < n){
    if(proc->killed){
      release(&tickslock);
      return -1;
    }
    sleep(&ticks, &tickslock);
  }
  release(&tickslock);
  return 0;
}

// return how many clock tick interrupts have occurred
// since boot.
int
sys_uptime(void)
{
  uint xticks;
  
  acquire(&tickslock);
  xticks = ticks;
  release(&tickslock);
  return xticks;
}

// Custom syscalls

int sys_clone(void) {
  // Declare vars
  void *arg;
  void *stack;
  
  // Validate before returning the clone
  void (*fcn) (void*);
  if ((argptr(0, (void *)&fcn, sizeof(void *)) < 0) || (argptr(2, (void *)&stack, sizeof(void *)) < 0) || (argptr(1, (void*)&arg, sizeof(void*)) < 0)){
    return -1;
  }
  else{
    return clone(fcn, arg, stack);
  }
}

int sys_join(void) {

  void ** stack = NULL;
  
  int retVal = argptr(0, (void*)&stack, sizeof(void**));
  if (retVal >= 0){
    return join(stack);
  }
  else
  {
    return -1;
  }
}

int sys_initcv(void)
{
  void * tmp_cond = NULL;

  if(argptr(0, (void*)&tmp_cond, sizeof(void*)) >= 0){
    struct cond_t* cond = (cond_t*)tmp_cond;
    initcv(cond);
    return 0;
  }
  else{
    return -1;
  }
}


int sys_wakecv(void)
{
  void * tmp_cond = NULL;

  if(argptr(0, (void*)&tmp_cond, sizeof(void*)) >= 0){
    struct cond_t* cond = (cond_t*)tmp_cond;
    wakecv(cond);
    return 0; 
  }
  else{
    return -1;
  }
}


int sys_sleepcv(void)
{
  void * cond = NULL;
  void * lock = NULL;
 
  if((argptr(1, (void*)&lock, sizeof(void*)) < 0) || (argptr(0, (void*)&cond, sizeof(void*)) < 0)){
    return -1;
  }
  else{
    sleepcv(cond, lock);
    return 0;
  }
}



