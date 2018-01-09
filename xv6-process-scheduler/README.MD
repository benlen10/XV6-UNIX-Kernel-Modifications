# XVX UNIX Process Schuduler Modfication

### Description
- This kernel modification is based on a project for CS537 - Operating Systems at UW Madison
- 
- Implement a basic MLFQ scheduler and FIFO scheduling method within the XV6 kernel
- 
### Implementation Details
-	This custom scheduler supports 4 different priority levels (3 being the highest and 0 the lowest)
-	Processes at priority 0 will execute until completion
- Whenever the xv6 10 ms timer tick occurs, the highest priority ready process is scheduled to run
- The highest priority ready process is scheduled to run whenever the previously running process exits, sleeps, or otherwise yields the CPU.
- If there are more than one processes on the same priority level, then you scheduler should schedule all the processes at that particular level in a round robin fashion. Except for priority level 0, which will be scheduled using FIFO basis.
- When a timer tick occurs, whichever process was currently using the CPU should be considered to have used up an entire timer tick's worth of CPU, even if it did not start at the previous tick (Note that a timer tick is different than the time-slice.)
- The time-slice associated with priority 3 is 8 timer ticks; for priority 2 it is 16 timer ticks; for priority 1 it is 32 timer ticks, and for priority 0 it executes the process until completion.
When a new process arrives, it should start at priority 3 (highest priority).
- If no higher priority job arrives and the running process does not relinquish the CPU, then that process is scheduled for an entire time-slice before the scheduler switches to another process.
- At priorities 3, 2, and 1, after a process consumes its time-slice it should be downgraded one priority. At priority 0, the process should be executed to completion.
- If a process voluntarily relinquishes the CPU before its time-slice expires at a particular priority level, its time-slice should not be reset; the next time that process is scheduled, it will continue to use the remainder of its existing time-slice at that priority level.
- To overcome the problem of starvation, we will implement a mechanism for priority boost. If a process has waited 10x the time slice in its current priority level, it is raised to the next higher priority level at this time (unless it is already at priority level 3). For priority 0, which does not have a time slice, processes that have waited 500 ticks should be raised to priority 1.