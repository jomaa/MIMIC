(******************************************************************************)
(*  © Université Lille 1 (2014-2017)                                          *)
(*                                                                            *)
(*  This software is a computer program whose purpose is to run a minimal,    *)
(*  hypervisor relying on proven properties such as memory isolation.         *)
(*                                                                            *)
(*  This software is governed by the CeCILL license under French law and      *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(******************************************************************************)

Require Import List Streams Omega.
Import List.ListNotations .
Require Import  HMonad Properties ProcessManager Step.

Set Printing Projections.



CoFixpoint intr : Stream (option nat) :=  
 Cons None (Cons None (Cons None (Cons None (Cons None
(Cons None (Cons None (Cons None (Cons (Some 0) 
(Cons None (Cons (Some 3)(Cons None (Cons None 
(Cons None (Cons None (Cons None (Cons None 
(Cons None (Cons None (Cons None (Cons (Some 0) 
(Cons None (Cons None (Cons None (Cons (Some 2) (Cons None  intr))))))))))))))))))))))))).

Definition progr := [Switch_process (*0*); Iret         (*1*); Nop           (*2*); Add_pte 3 1   (*3*); 
                     Write 16 17    (*4*); Load 17      (*5*); Free 17       (*6*); Exit          (*7*); 
                     Trap 1         (*8*); Add_pte 3 1  (*9*); Add_pte 3 2  (*10*); Write 102 17 (*11*); 
                     Nop           (*12*); Load 17     (*13*); Free 17      (*14*); Exit         (*15*); 
                     Halt          (*16*); Load 2      (*17*); Nop          (*18*); Iret         (*19*); 
                  Create_process 2 (*20*); Iret        (*21*); Nop          (*22*); Iret         (*23*)].


Definition init := 
{|
  process_list := [{| eip := 8; process_kernel_mode := false; cr3_save := 1; stack_process := [] |}];
  current_process := {| eip := 8; process_kernel_mode := false; cr3_save := 1; stack_process := [] |};
  cr3 := 1;
  intr_table := [0; 20; 16; 22];
  interruptions := intr;
  kernel_mode := false;
  pc := 8;
  code := progr;
  stack := [];
  register :=0; 
  first_free_page := 2;
  data :=  [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0; 
            0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0; 
            3;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0; 
            4;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0; 
            5;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;
            6;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;
            7;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;
            8;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0] |} .
Definition boot := 
modify (fun s => init ).
(*
Eval vm_compute in run (loop 0) init. (* interrupt 3 *)
Eval vm_compute in run (loop 1) init. (* create new process *)
Eval vm_compute in run (loop 2) init. (* Iret *)
Eval vm_compute in run (loop 3) init. (* Nop *) 
Eval vm_compute in run (loop 4) init. (* Add_pte 3 1 *)
Eval vm_compute in run (loop 5) init. (* Add_pte *) 
Eval vm_compute in run (loop 6) init. (* write 102 17*)
Eval vm_compute in run (loop 7) init. (* Nop *)
Eval vm_compute in run (loop 8) init. (* load 17 *)
Eval vm_compute in run (loop 9) init. (* interruption : some 0 => switch_process *) 
Eval vm_compute in run (loop 10) init. (* switch_process *) 
Eval vm_compute in run (loop 11) init. (* Interruption : some 1 => Nop *)
Eval vm_compute in run (loop 12) init. (* Nop *)
Eval vm_compute in run (loop 13) init. (* Iret *)
Eval vm_compute in run (loop 14) init. (* Iret *)
Eval vm_compute in run (loop 15) init. (* Nop *)
Eval vm_compute in run (loop 16) init. (* Add_pte *) 
Eval vm_compute in run (loop 17) init. (* write 16 17 *) 
Eval vm_compute in run (loop 18) init. (* load 17 *)
Eval vm_compute in run (loop 19) init. (* Free 17 *)
Eval vm_compute in run (loop 20) init. (* Exit *) (*** load 17 *)
Eval vm_compute in run (loop 21) init. (* Interruption : Some 0 *) 
Eval vm_compute in run (loop 22) init. (* switch_process *) 
Eval vm_compute in run (loop 23) init. (* Iret *)
Eval vm_compute in run (loop 24) init. (* Free 17 *)
Eval vm_compute in run (loop 25) init. (* Interruption : Some 2 *)
Eval vm_compute in run (loop 26) init. (* Halt *)
Eval vm_compute in run (loop 27) init.
Eval vm_compute in run (loop 28) init.
Eval vm_compute in run (loop 29) init.
Eval vm_compute in run (loop 30) init.
Eval vm_compute in run (loop 31) init.
Eval vm_compute in run (loop 32) init.
Eval vm_compute in run (loop 33) init.
Eval vm_compute in run (loop 34) init.
Eval vm_compute in run (loop 35) init.
Eval vm_compute in run (loop 36) init.
Eval vm_compute in run (loop 37) init.
Eval vm_compute in run (loop 38) init.
Eval vm_compute in run (loop 39) init.
*)
Lemma init_invariant : 
{{fun s => True }} boot 
{{fun _ s => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
unfold boot.
eapply weaken.
eapply modify_wp.
simpl.
intros.
split.
(** isolation **)
unfold isolation.
simpl.
intros.
destruct H0 as [H0 | H0]; [| now contradict H0].
destruct H1 as [H1 | H1]; [| now contradict H1].
subst.
simpl in *.   
now contradict H2.
(** consistent **)
unfold consistent.
simpl.
intuition.
(** really_free **)
+ unfold really_free.
simpl.
do 6 (constructor 2;
unfold nb_page;
unfold page_size;
cbn; try
omega).
constructor 1.
unfold nb_page;
unfold page_size;
cbn; try
omega
simpl. omega.
(** not_cyclic **)
+ unfold not_cyclic.
simpl.
do 6 (constructor 2;
unfold nb_page;
unfold page_size;
cbn; try
omega).
constructor 1;
unfold nb_page;
unfold page_size;
cbn; try
omega.
(** memory_length **)
+ unfold memory_length.
simpl. omega.
(** noDuplic_processPages**)
+ unfold noDuplic_processPages.
simpl. intros. destruct H0 as [H0 | H0]; [| now contradict H0].
unfold PageTableManager.process_used_pages.
simpl.
unfold PageTableManager.get_mapped_pte.
constructor.
rewrite in_map_iff.
subst.
simpl.
unfold not;intros.
destruct H0;intuition.
subst.
simpl. constructor.
(** page_notZero **)
+ unfold page_notZero.
unfold used_notZero, free_notZero.
simpl.
split;intros.
 destruct H0 as [H0 | H0]; [| now contradict H0].
 unfold PageTableManager.get_mapped_pte in *.
 destruct H1 as [H1 | H1].
 subst.
 simpl.
 unfold nb_page;
unfold page_size;
cbn; try
omega.
subst.
simpl in *.
now contradict H1.
do 6 (constructor 2;
unfold nb_page;
unfold page_size;
cbn; try
omega).
constructor 1;
unfold nb_page;
unfold page_size;
cbn; try
omega.
(** currProcess_inProcessList **)
+ unfold currProcess_inProcessList.
simpl.
exists {| eip := 8; process_kernel_mode := false; cr3_save := 1; stack_process := [] |}.
simpl.
intuition.
Qed.