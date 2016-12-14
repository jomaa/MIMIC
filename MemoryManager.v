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

Require Import FunctionalExtensionality Bool List Streams Arith NPeano Omega.
Import List.ListNotations.
Require Import Lib StateMonad HMonad.

Definition update_memory (l : list nat) :  M unit  := 
modify (fun s =>  {|
    process_list := s.(process_list);
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
    data := l |}). 

Lemma update_memory_wp (l : list nat)   (P : unit -> state -> Prop) :
{{ fun s => P tt {|
     process_list := s.(process_list);
     current_process := s.(current_process);
     cr3:= s.(cr3);
     intr_table:= s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := l   
  |}
}} update_memory l {{ P }}.
Proof.
eapply modify_wp.
Qed.


Definition update_first_free_page (new_first_free_page : nat)  : M unit := 
modify (fun s => {|
    process_list := s.(process_list);
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    code := s.(code);
    stack := s.(stack); 
    register := s.(register);
    first_free_page := new_first_free_page ;
    data := s.(data)
    |} ).

Lemma update_first_free_page_wp (new_first_free_page : nat)  (P : unit -> state -> Prop) :
{{ fun s => P tt {|
       process_list := s.(process_list);
    current_process := s.(current_process);
  
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := s.(kernel_mode);
    pc := s.(pc);
    code := s.(code);
    stack := s.(stack); 
    register := s.(register);
    first_free_page := new_first_free_page ;
    data := s.(data)   
  |}
}} update_first_free_page new_first_free_page  {{ P }}.
Proof.
apply modify_wp.
Qed.

Definition get_next_free_page : M nat :=
perform s := get in 
let next_free_page := List.nth (s.(first_free_page)*page_size) s.(data) nb_page  in  ret next_free_page.

Lemma get_next_free_page_wp (P : nat -> state -> Prop) : 
{{ fun s : state =>  exists  next_free_page ,         
       next_free_page = List.nth (s.(first_free_page)*page_size) s.(data) nb_page /\  P next_free_page s 
}} get_next_free_page  {{ P }}.
Proof.
unfold get_next_free_page.
eapply bind_wp.
 - intro s. eapply weaken.  eapply ret_wp. intros. pattern s , s0.  eassumption.
 - eapply weaken.  eapply get_wp. intros. simpl.  firstorder. subst . assumption.
Qed.

Definition alloc_page  : M (nat+unit) := 
perform s := get in 
let new_first_free_page :=  List.nth (s.(first_free_page)*page_size) s.(data) nb_page in 
if lt_dec s.(first_free_page) nb_page then 
 update_first_free_page new_first_free_page ;; ret (inl s.(first_free_page))  else ret (inr tt).

Lemma alloc_page_wp (P : (nat+unit) -> state -> Prop)  :
 {{fun s : state =>  
( ( s.(first_free_page) < nb_page /\ 
( P (inl s.(first_free_page) ) 
  {| process_list := s.(process_list);
     current_process := s.(current_process);
     cr3 := s.(cr3);
     intr_table := s.(intr_table);
     interruptions := s.(interruptions);
     kernel_mode := s.(kernel_mode);
     pc := s.(pc);
     code := s.(code);
     stack := s.(stack); 
     register := s.(register);
     first_free_page := List.nth (s.(first_free_page)*page_size) s.(data) nb_page;
     data := s.(data)   
  |})) \/ s.(first_free_page) >= nb_page /\ P (inr tt) s )}} alloc_page {{P}}.
Proof.

eapply bind_wp_rev. 
+ eapply weaken.  apply get_wp. intros. simpl.
instantiate (1:= fun s s' => s=s' /\ (first_free_page s < nb_page /\
    P (inl (first_free_page s))
      {|
      process_list := process_list s;
      current_process := current_process s;
      cr3 := cr3 s;
      code := code s;
      intr_table := intr_table s;
      interruptions := interruptions s;
      kernel_mode := kernel_mode s;
      pc := pc s;
      stack := stack s;
      register := register s;
      data := data s;
      first_free_page := List.nth (first_free_page s * page_size) (data s)
                           nb_page |} \/
    first_free_page s >= nb_page /\ P (inr tt) s) ).
 simpl. intuition.  
+ intro s.  
 destruct (lt_dec (first_free_page s) nb_page).
 - simpl. eapply bind_wp_rev.
   * eapply weaken.  eapply update_first_free_page_wp.
     simpl. intros. destruct H.  
      intuition.
      { subst s0.
          instantiate (1:= fun (_ : unit) (s1 : state') => s1 = {|
       process_list := process_list s;
       current_process := current_process s;
       cr3 := cr3 s;
       code := code s;
       intr_table := intr_table s;
       interruptions := interruptions s;
       kernel_mode := kernel_mode s;
       pc := pc s;
       stack := stack s;
       register := register s;
       data := data s;
       first_free_page := List.nth (first_free_page s * page_size) (data s)
                            nb_page |}  /\P (inl (first_free_page s))  {|
       process_list := process_list s;
       current_process := current_process s;
       cr3 := cr3 s;
       code := code s;
       intr_table := intr_table s;
       interruptions := interruptions s;
       kernel_mode := kernel_mode s;
       pc := pc s;
       stack := stack s;
       register := register s;
       data := data s;
       first_free_page := List.nth (first_free_page s * page_size) (data s)
                            nb_page |} ).
         simpl. split. reflexivity.  assumption. }
     { contradict H0. intuition. 
     }
   * intros [].  simpl.  eapply weaken. apply ret_wp. intros. destruct H.  subst. assumption.
 -  simpl . eapply weaken.  apply ret_wp. intros. destruct H. 
    destruct H0.
     * destruct H0.  contradict H0.  assumption.
     * destruct H.  simpl. intuition.
Qed.




(*
Fixpoint  destroy_process (cr3 : nat)  (page_table : list nat) : M unit := 
match page_table with 
|nil => free_page cr3
|0::l => destroy_process cr3 l 
|a::l => free_page ((getBase a permission_size ) ) ;; destroy_process cr3 l 
end .

Definition free : M unit :=
  perform s := get in
  let page_table := sublist (s.(cr3) * page_size) page_size s.(data)  in
  destroy_process s.(cr3) page_table.

Definition exit : M unit :=
perform s := get in 
perform l := tl s.(process_list) in 
match l with 
nil =>  put {|
    process_list := l;
    current_process := s.(current_process);
    cr3 := s.(cr3);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := true;
    pc := 11;
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
      first_free_page := s.(first_free_page);
    data := s.(data) |}
| _ =>
perform process := hd l in
let eip := process.(eip) in  
  put {|
    process_list := l;
    current_process := process;
    cr3 := process.(cr3_save);
    intr_table := s.(intr_table);
    interruptions := s.(interruptions);
    kernel_mode := process.(process_kernel_mode);
    pc := eip;
    code := s.(code);
    stack := s.(stack);
    register := s.(register);
    first_free_page := s.(first_free_page);
    data := s.(data) |}
end.
*)
