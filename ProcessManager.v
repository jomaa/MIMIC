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
Require Import Lib StateMonad HMonad MMU PageTableManager MemoryManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

(** add new process **) 
Definition add_new_process (cr3_p : nat) (eip_p : nat) : M unit := 
modify (fun s =>  {| process_list := {| eip :=eip_p; process_kernel_mode := false; cr3_save := cr3_p;stack_process:= []|} ::s.(process_list);
                     current_process := s.(current_process);
                     cr3 := s.(cr3);
                     intr_table := s.(intr_table);
                     interruptions := s.(interruptions);
                     kernel_mode := s.(kernel_mode);
                     pc := s.(pc);
                     code := s.(code);
                     stack := s.(stack); 
                     register := s.(register);
                     first_free_page := s.(first_free_page);
                     data := s.(data) |}) .

(** add new process WP **) 
Lemma add_new_process_wp (cr3_p eip_p : nat) (P : unit-> state-> Prop) :
{{fun s => P tt {| process_list := {| eip :=eip_p; process_kernel_mode := false; cr3_save := cr3_p; stack_process := []|} ::s.(process_list);
                   current_process := s.(current_process);
                   cr3 := s.(cr3);
                   intr_table := s.(intr_table);
                   interruptions := s.(interruptions);
                   kernel_mode := s.(kernel_mode);
                   pc := s.(pc);
                   code := s.(code);
                   stack := s.(stack); 
                   register := s.(register);
                   first_free_page := s.(first_free_page);
                   data := s.(data) |}
}}
add_new_process cr3_p eip_p {{ P }}.
Proof. 
apply modify_wp.
Qed.

Definition create_process eip : M unit :=
perform page := alloc_page in 
match page  with 
|inl cr3 => init_process_page_table cr3 ;; add_new_process cr3 eip 
|inr _ => ret tt
end.

Definition init_current_process  : M unit :=
modify (fun s => {|
    process_list := s.(process_list);
    current_process := List.hd
                         {|
                         eip := 0;
                         process_kernel_mode := false;
                         cr3_save := 0;
                         stack_process := [] |} s.(process_list);
    cr3 := (List.hd
              {|
              eip := 0;
              process_kernel_mode := false;
              cr3_save := 0;
              stack_process := [] |} s.(process_list)).(cr3_save);
    code := s.(code);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    stack := [((List.hd
                  {|
                  eip := 0;
                  process_kernel_mode := false;
                  cr3_save := 0;
                  stack_process := [] |} s.(process_list))
               .(process_kernel_mode),
              (List.hd
                 {|
                 eip := 0;
                 process_kernel_mode := false;
                 cr3_save := 0;
                 stack_process := [] |} s.(process_list)).(eip))];
    register := s.(register);
    data := s.(data);
    first_free_page := s.(first_free_page) |}).


Lemma init_current_process_wp  (P : unit-> state-> Prop) :
{{fun s => P tt {|
    process_list := s.(process_list);
    current_process := List.hd
                         {|
                         eip := 0;
                         process_kernel_mode := false;
                         cr3_save := 0;
                         stack_process := [] |} s.(process_list);
    cr3 := (List.hd
              {|
              eip := 0;
              process_kernel_mode := false;
              cr3_save := 0;
              stack_process := [] |} s.(process_list)).(cr3_save);
    code := s.(code);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    stack := [((List.hd
                  {|
                  eip := 0;
                  process_kernel_mode := false;
                  cr3_save := 0;
                  stack_process := [] |} s.(process_list))
               .(process_kernel_mode),
              (List.hd
                 {|
                 eip := 0;
                 process_kernel_mode := false;
                 cr3_save := 0;
                 stack_process := [] |} s.(process_list)).(eip))];
    register := s.(register);
    data := s.(data);
    first_free_page := s.(first_free_page) |}
}}
init_current_process {{ P }}.
Proof. 

apply modify_wp.
Qed.




Definition reset : M unit:= 
create_process 2 ;; create_process 8;; init_current_process . 
