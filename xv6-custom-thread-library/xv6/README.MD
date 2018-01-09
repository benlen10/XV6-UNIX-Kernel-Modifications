## CS537 OS Project 4B XV6 - (XV6 Kernel Threads) (Updated Regrade Submission)

###	Brief Summary: 
- I’ve modified my original submission to resolve some of the preexisting bugs and improve the test pass rate. I’ve included a list of notable changes below 

### Notable Changes:
- Implement initcv, sleepcv and wakecv syscalls within kernel/proc.c

- Modify thread_join within user/umalloc.c to return -1 if the join() call returns zero

- Move lock_init, lock_acquire and thread_release from user/ulib.c to user/umalloc.c

- Within kernel/proc.c, modify growproc() method to update proc sizes and join() to properly detect threads


Thank you very much for your time,


Ben
