(******************************************************************************)
(*  © Université Lille 1 (2014-2016)                                          *)
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

Require Import List Arith NPeano Coq.Logic.JMeq Coq.Logic.Classical_Prop.
Import List.ListNotations .
Require Import Lib StateMonad HMonad MMU Alloc_invariants 
Properties LibOs PageTableManager MemoryManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Definition default_process :=  
{| cr3_save := 0; eip:=0; process_kernel_mode := true ; stack_process := [] |} .

Definition default_stack := 
(false , 0).
(** * Process management *)

Definition update_process (c : process)(pc cr3: nat)  : process :=
{| cr3_save := cr3; eip:=pc; process_kernel_mode :=c.(process_kernel_mode) ; stack_process := c.(stack_process) |} .

Definition enqueuelist {A : Type} (l : list A) (a: A) : list A :=
l ++ [a].

Definition update_list_process (l :list process) : M unit :=
    modify (fun s => {|
  process_list := l;
  current_process := s.(current_process);
  code := s.(code) ;
  cr3 := s.(cr3);
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := s.(stack);
  register := s.(register);
  first_free_page := s.(first_free_page);
  data := s.(data) 

|}).

Lemma update_list_process_wp (l :list process) (P : unit -> state -> Prop) :
  {{ fun s => P tt {|
   process_list := l;
  current_process := s.(current_process);
   cr3 := s.(cr3);
  code := s.(code) ;
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := s.(stack);
  register := s.(register);
    first_free_page := s.(first_free_page);
  data := s.(data)    
  |}
}} update_list_process l {{ P }}.
Proof.
apply modify_wp.
Qed.

Definition save_process : M unit := 
perform s := get in(* get state*)
let process := s.(current_process) in (* get next process*)
let a := List.hd default_stack s.(stack) in 
let eip := snd a in
let new_process := update_process process eip s.(cr3)in 

let list_process := List.tl s.(process_list) in 
let l := enqueuelist list_process new_process in update_list_process l.

Lemma  save_process_wp (P : unit -> state -> Prop) :
  {{ fun s =>  P tt  {|
  process_list := enqueuelist (List.tl s.(process_list))
                    (update_process s.(current_process)
                       (snd (List.hd default_stack s.(stack))) s.(cr3));
  current_process := s.(current_process);
  cr3 := s.(cr3);
  code := s.(code);
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := s.(stack);
  register := s.(register);
  data := s.(data);
  first_free_page := s.(first_free_page) |}
}}
save_process
{{ P }}.
Proof.
unfold save_process.
eapply bind_wp.
 + intro s.
   eapply update_list_process_wp.
 + eapply weaken.
  eapply get_wp. 
  intros. 
  simpl.
  assumption.
Qed.

Definition restore_process : M unit :=
perform s := get in
let process := List.hd default_process s.(process_list) in
let h' := List.hd default_stack s.(stack) in 
let new_stack := List.tl s.(stack) in 
let km := process.(process_kernel_mode) in
let eip := process.(eip)in 
  modify (fun s => {|
  process_list := s.(process_list);
  current_process := process;
  cr3 := process.(cr3_save);
  intr_table := s.(intr_table);
  interruptions :=  s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := (km, eip)::new_stack;
  register := s.(register);
  data := s.(data) ;
  first_free_page := s.(first_free_page);
  code := s.(code)
|}).


Lemma  restore_process_wp  (P : unit -> state -> Prop) :
  {{ fun s => P tt
  {|
  process_list := s.(process_list);
  current_process := List.hd default_process s.(process_list);
  cr3 := (List.hd default_process s.(process_list)).(cr3_save);
  code := s.(code);
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := ((List.hd default_process s.(process_list)).(process_kernel_mode),
           (List.hd default_process s.(process_list)).(eip))
           :: List.tl s.(stack);
  register := s.(register);
  data := s.(data);
  first_free_page := s.(first_free_page) |}
}}
restore_process
{{ P }}.
Proof. 
unfold restore_process.
eapply bind_wp.
 + intro s. 
   eapply modify_wp. 
 + eapply weaken.
  eapply get_wp. 
  intros. 
  simpl.
  assumption.
Qed.


Definition switch_process :=

  save_process ;; restore_process.
