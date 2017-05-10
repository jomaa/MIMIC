# Summary

This project is a formal proof of an abstract model of a microkernel which supports preemptive scheduling and ensures memory isolation.  
# Dependency 

Coq 8.6

# Folder content

   * Makefile
   * Readme.md
   * *.v files

# FILES STRUCTURE

This project is organized in the following way.

* The definition of our hardware monad that provides states is split
  in the two files StateMonad.v and HMonad.v.

* Our model of a hardware architecture is split into different files:

  * he hardware component translate for the MMU is singled out in MMU.v.

  * Memory allocation is modeled in MemoryManager.v by the alloc\_page subroutine.

  * Access to physical memory is modeled in Access.v where the instructions write and read are defined.

  * The dynamic evolution of the system (i.e. step), including interrupt
  management (interrupt, fetch\_interrupt, fetch\_instruction
  and return\_from\_interrupt), is modeled in Instructions.v and
  Step.v.

* Our model of a microkernel is split into different files:

  * Subroutines add\_pte and remove_pte to modify page tables are in
    PageTableManager.v.

  * Subroutines save\_process, restore\_process and switch\_process for
    preemptive CPU-time sharing are in Scheduler.v.

  * The process creation subroutine create\_process is defined in ProcessManager.v.

* The file Properties.v contains the definitions of isolation and
  consistency.
 
* The proofs of preservation of isolation and consistency are spread
  between the files MMU\_invariant.v, Write\_invariants.v,
  Scheduler\_invariant.v, Instructions\_invariants.v,
  ProcessManager\_invariant.v, Step\_invariant.v, Alloc\_invariants.v,
  Addpte\_invariant.v and Removepte\_invariant.v.

# Building the proof

Build:
   :-$ make

Clean:
   :-$ make clean

