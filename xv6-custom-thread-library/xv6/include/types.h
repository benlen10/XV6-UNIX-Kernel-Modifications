#ifndef _TYPES_H_
#define _TYPES_H_

// Type definitions
typedef unsigned int   uint;
typedef unsigned short ushort;
typedef unsigned char  uchar;
typedef uint pde_t;

// Custom lock_t definition
typedef struct __lock_t {
  uint is_locked;
} 
lock_t;

// Custoom cond_t definition
typedef struct cond_t { 
  int size;
  int head;
  int tail; 
  int* pids; 
} 
cond_t;



#ifndef NULL
#define NULL (0)
#endif

#endif //_TYPES_H_
