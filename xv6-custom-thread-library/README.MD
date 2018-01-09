## XV6 Custom Thread Library

### Description 
- Based upon a Project for CS537 - Operating Systems at UW Madison
- Implement two new syscalls, clone() and join() within the xv6 UNIX kernel

### Implementation Notes
- The parameter arg in clone() can be a NULL pointer, and clone() should not fail.
- The thread can clone another thread but will not fork another process.
- When thread A clones another thread B, the parent of thread B should be A, NOT the parent of A. Note that parent of thread A, thread A and thread B should share the same address space.
