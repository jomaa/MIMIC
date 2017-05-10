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

Require Import FunctionalExtensionality Bool List Streams Arith NPeano Omega.
Import List.ListNotations.
Require Import Lib StateMonad HMonad MMU Alloc_invariants
 Properties LibOs MMU_invariant PageTableManager MemoryManager. 

(** Hardwired basic instructions *)

Definition fetch_interruption : M (option nat) :=
  perform s := get in
  perform _ := put {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := Streams.tl s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) |} in
  ret (Streams.hd (interruptions s)).


Lemma fetch_interruption_wp (P :option nat -> state -> Prop) :
  {{ fun s => P (Streams.hd (interruptions s)) {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := Streams.tl s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc); code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) |} }} fetch_interruption {{ P }}.
Proof.
eapply  bind_wp.
intro.  eapply bind_wp.
intros []. eapply weaken.
apply ret_wp.
instantiate (1 := fun _ s => P _ _). simpl. intros. eassumption.
eapply weaken.
apply put_wp.
instantiate (1 := fun s _ => P _ _); simpl; intros; eassumption.
eapply weaken.
apply get_wp.
trivial.
Qed.




Definition fetch_instruction : M instr :=
  perform s := get in
if lt_dec s.(pc) (length s.(code)) then 
 nth s.(pc) s.(code)
else ret Halt.
 
Lemma fetch_instruction_wp (P : instr -> state -> Prop) :
  {{ fun s => s.(pc) < length s.(code) /\ (forall d : instr, P (List.nth (pc s) (code s) d) s) \/
              s.(pc) >= length s.(code) /\  P Halt s   }} fetch_instruction {{ P }}.
Proof.
unfold fetch_instruction.
eapply bind_wp.
intros s. 

instantiate (1 := fun a s => s = a /\ (pc s < length (code s) /\
   (forall d : instr, P (List.nth (pc s) (code s) d) s) \/
   pc s >= length (code s) /\  P Halt s)).
   simpl. 
case_eq (lt_dec (pc s) (length (code s))).
 + intros.
   eapply weaken.
   eapply nth_wp.
   intros.
   simpl.
   destruct H0. 
   subst. 
   intuition.
   contradict H1.
   intuition.
 + intros. 
   eapply weaken.
   apply ret_wp.
   intros.
   destruct H0.
   subst. 
   intuition.
   contradict H1.
   intuition.
 + eapply weaken.
   eapply get_wp.
   intros.
   simpl.
   destruct H. 
   intuition.
   intuition.
Qed.



Definition incr_pc : M unit :=
  modify (fun s => {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := S s.(pc);
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) |}).

Lemma incr_pc_wp (P : unit -> state -> Prop) :
  {{ fun s => P tt {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := S s.(pc);
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) |} }} incr_pc {{ P }}.
Proof.
apply modify_wp.
Qed.




Definition interrupt (n : nat) : M unit :=
  perform s:= get in
if lt_dec n (length (intr_table s)) then 
  perform addr := nth n s.(intr_table) in
  put {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := true;
    pc := addr;
    code := s.(code);
    stack := (s.(kernel_mode), s.(pc))::s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data)|}
else ret tt.

Lemma interrupt_wp (n : nat) (P : unit -> state -> Prop) :
  {{ fun s =>
    n < length s.(intr_table) /\
    (forall d : nat, P tt {|
      process_list := s.(process_list);
      current_process := s.(current_process);
      cr3 := s.(cr3);
      intr_table := s.(intr_table);
      interruptions := s.(interruptions);
      kernel_mode := true;
      pc := List.nth n s.(intr_table) d;
      code := s.(code);
      stack := (s.(kernel_mode), s.(pc)) :: s.(stack);
      register := s.(register);
      first_free_page := s.(first_free_page);
      data := s.(data) |}) \/  n >= length s.(intr_table) /\ P tt s}} interrupt n {{ P }}.
Proof.
unfold interrupt.
eapply bind_wp.
intros s. 

instantiate (1 := fun a s => s = a /\ ( n < length s.(intr_table)  /\
   (forall d : nat, P tt {|
      process_list := s.(process_list);
      current_process := s.(current_process);
      cr3 := s.(cr3);
      intr_table := s.(intr_table);
      interruptions := s.(interruptions);
      kernel_mode := true;
      pc := List.nth n s.(intr_table) d;
      code := s.(code);
      stack := (s.(kernel_mode), s.(pc)) :: s.(stack);
      register := s.(register);
      first_free_page := s.(first_free_page);
      data := s.(data) |}) \/
    n >= length s.(intr_table)  /\  P tt s)).
   simpl. 
case_eq (lt_dec n (length (intr_table s))).
 + intros.
   eapply weaken.
   eapply bind_wp.
   intros.
   apply put_wp.
   eapply nth_wp.
   intros.
   simpl.
   destruct H0. 
   subst. 
   intuition.
   contradict H1.
   intuition.
 + intros. 
   eapply weaken.
   apply ret_wp.
   intros.
   destruct H0.
   subst. 
   intuition.
   contradict H1.
   intuition.
 + eapply weaken.
   eapply get_wp.
   intros.
   simpl.
   destruct H. 
   intuition.
   intuition.
Qed.



Definition return_from_interrupt : M unit :=
  perform s:= get in
 let h := List.hd (false , 0) s.(stack) in
 let t := List.tl s.(stack) in
  put {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := fst h;
    pc := snd h;
    code := s.(code);
    stack := t;
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) |}.

Lemma return_from_interrupt_wp (P : unit -> state -> Prop) : {{
  fun s =>

    P tt
  {|
  process_list := process_list s;
  current_process := current_process s;
  cr3 := cr3 s;
  code := code s;
  intr_table := intr_table s;
  interruptions := interruptions s;
  kernel_mode := fst (List.hd (false, 0) (stack s));
  pc := snd (List.hd (false, 0) (stack s));
  stack := List.tl (stack s);
  register := register s;
  data := data s;
  first_free_page := first_free_page s |}
}} return_from_interrupt {{ P }}.
Proof.
repeat (eapply bind_wp; intros).
eapply weaken.
apply put_wp.
instantiate (1 := fun s _ => P _ _); simpl; intros; eassumption.

eapply weaken.
apply get_wp.
simpl.
intros s H1.
repeat esplit; eassumption.
Qed.


(** * Add an hardware interruption to be dealt with at the next cycle *)

Definition add_interruption (I : option nat) : M unit := 
 modify (fun s => {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := Cons I (s.(interruptions));
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data)    
  |}).

Lemma add_interruption_wp (I : option nat) (P : unit -> state -> Prop) :
  {{ fun s => P tt {|
      process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := Cons I (s.(interruptions));
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) 
  |}
}} add_interruption I {{ P }}.
Proof.
apply modify_wp.
Qed.

