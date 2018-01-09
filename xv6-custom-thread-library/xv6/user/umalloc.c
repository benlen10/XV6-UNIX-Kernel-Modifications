#include "types.h"
#include "stat.h"
#include "x86.h"
#include "user.h"
#include "param.h"

// Memory allocator by Kernighan and Ritchie,
// The C programming Language, 2nd ed.  Section 8.7.

// The current pagesize
#define PGSIZE (4096)

typedef long Align;

union header {
  struct {
    union header *ptr;
    uint size;
  } s;
  Align x;
};

typedef union header Header;

static Header base;
static Header *freep;

void
free(void *ap)
{
  Header *bp, *p;

  bp = (Header*)ap - 1;
  for(p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)
    if(p >= p->s.ptr && (bp > p || bp < p->s.ptr))
      break;
  if(bp + bp->s.size == p->s.ptr){
    bp->s.size += p->s.ptr->s.size;
    bp->s.ptr = p->s.ptr->s.ptr;
  } else
    bp->s.ptr = p->s.ptr;
  if(p + p->s.size == bp){
    p->s.size += bp->s.size;
    p->s.ptr = bp->s.ptr;
  } else
    p->s.ptr = bp;
  freep = p;
}

static Header*
morecore(uint nu)
{
  char *p;
  Header *hp;

  if(nu < 4096)
    nu = 4096;
  p = sbrk(nu * sizeof(Header));
  if(p == (char*)-1)
    return 0;
  hp = (Header*)p;
  hp->s.size = nu;
  free((void*)(hp + 1));
  return freep;
}

// Custom join (wait) func, utilizing the join() syscall
int thread_join() {

  // Fetch the pid after waiting on the other proc
  void *stack = NULL;
  int pid_ret = join(&stack);
  if(pid_ret != 0)
  {
    return pid_ret;
  }
  else{
    free(stack);
    return -1;
  }
}

// Custom create (wait) func, utilizing the clone() syscall
int thread_create(void (*start_routine)(void*), void *arg) {
  int stack_addr = -1;
  
  // Allocate and validate the stack
  void *stack_cur = malloc(PGSIZE);

  uint stackVal = (((uint) stack_cur) % PGSIZE);
  if(stackVal == 0) {
    stack_addr = (uint) stack_cur;
  } else {
    free(stack_cur);
    stack_cur = malloc(2 * PGSIZE);
    stack_addr = (uint) stack_cur;
    stack_cur = stack_cur + (PGSIZE - ((uint) stack_cur) % PGSIZE);
  }

  ((uint*) stack_cur)[0] = stack_addr;
  return clone(start_routine, arg, stack_cur);
}

// Custom locking function

// Initalize the lock and set the initial is_locked value;
void lock_init(lock_t * lock_obj) {
  lock_obj->is_locked = 0;
}

// Attempt to aquire the lock specified by the lock_t pram
void lock_acquire(lock_t * lock_obj) {
  while (xchg( &lock_obj->is_locked, 1));
}

void lock_release(lock_t * lock_obj) {
  lock_obj->is_locked = 0;
}


void cond_init(cond_t* cond_param)
{
  cond_param = malloc(sizeof(struct cond_t));
  cond_param->pids = malloc(sizeof(int)*8);
  initcv(cond_param);
} 


void cond_wait(cond_t* cond_param, lock_t* lock_param)
{
  sleepcv(cond_param, lock_param);
}


void cond_signal(cond_t* cond_param)
{
  wakecv(cond_param);
}

void* malloc(uint nbytes)
{
  Header *p, *prevp;
  uint nunits;

  nunits = (nbytes + sizeof(Header) - 1)/sizeof(Header) + 1;
  if((prevp = freep) == 0){
    base.s.ptr = freep = prevp = &base;
    base.s.size = 0;
  }
  for(p = prevp->s.ptr; ; prevp = p, p = p->s.ptr){
    if(p->s.size >= nunits){
      if(p->s.size == nunits)
        prevp->s.ptr = p->s.ptr;
      else {
        p->s.size -= nunits;
        p += p->s.size;
        p->s.size = nunits;
      }
      freep = prevp;
      return (void*)(p + 1);
    }
    if(p == freep)
      if((p = morecore(nunits)) == 0)
        return 0;
  }
}
