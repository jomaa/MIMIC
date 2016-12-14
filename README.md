# Summary

This project is a formal proof of an abstract model of a microkernel
which supports preemptive scheduling and ensures memory isolation.

The source code is covered by the CeCILL-A license.
It was developed by:

- Narjes Jomaa
- David Nowak
- Gilles Grimaud
- Samuel Hym


# Dependency

Coq 8.5pl2


# Organization

This project is organized in the following way.

- The definition of our hardware monad that provides states is split
  in the two files `StateMonad.v` and `HMonad.v`.

- Our model of a hardware architecture is split into different files:

  - The hardware components for the MMU are in `MMU.v`.

  - Access to physical memory is modeled in `MemoryManager.v`.

  - The instruction write is singled out in `Write.v`.

  - The dynamic evolution of the system (including interruption
    management) is modeled in `Instructions.v` and `Step.v`.

- Our model of a microkernel is split into different files:

  - Subroutines `add_pte` and `remove_pte` to modify page tables are
    in `PageTableManager.v`.

  - Subroutines `save_process`, `restore_process` and `switch_process` for
    preemptive CPU-time sharing are in `Scheduler.v`.

  - Process creation and update are in `ProcessManager.v`.

- The file `Properties.v` contains the definitions of isolation and
  consistency.

- The proofs of preservation of isolation and consistency are spread
  between the files `MMU_invariant.v`, `Write_invariants.v`,
  `Scheduler_invariant.v`, `Instructions_invariants.v`,
  `ProcessManager_invariant.v`, `Step_invariant.v`, `Alloc_invariants.v`,
  `Addpte_invariant.v` and `Removepte_invariant.v`.


# Building the proof

Build:
   :-$ make

Clean:
   :-$ make clean

