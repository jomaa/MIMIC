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

Require Import List Arith NPeano Coq.Logic.JMeq Coq.Logic.Classical_Prop.
Import List.ListNotations .
Require Import Lib StateMonad HMonad MMU MemoryManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Definition get_mapped_pte cr3 data := 
List.map removePermission (List.filter isMapped_pte (sublist (cr3 *page_size) nb_pte  data)) .

Definition process_used_pages (data : list nat)   (p: process)  : list nat := 
[p.(cr3_save)]++ get_mapped_pte p.(cr3_save) data.

Definition all_used_pages (data : list nat) (process_list : list process) :=
List.flat_map (process_used_pages data)  process_list.

Definition get_cr3 (p : process) := 
p.(cr3_save).

Definition all_cr3 (process_list : list process) :=
List.map  get_cr3 process_list.

Definition any_mapped_page s cr3 : Prop :=
( List.map removePermission
          (filter isMapped_pte
             (sublist (cr3 * page_size) nb_pte s.(data)))) = []. 


(** update len elements -- 0 **)
Definition init_zero (start len : nat) (l: list nat) : list nat :=
  firstn start l ++ repeat len 0 ++ skipn (start + len) l.


(** init Page Table -- 0 **) 
Definition init_process_page_table cr3 : M unit := 
perform s := get in 
let memory := init_zero (cr3 * page_size)  page_size  s.(data) 
in update_memory  memory.

(** init process page table weakest precondition **) 
Lemma init_process_page_table_wp cr3_save (P : unit -> state -> Prop)  :
 {{fun s : state => P tt {| process_list := s.(process_list);
                                  current_process := s.(current_process);
                                  cr3 := s.(cr3);
                                  intr_table := s.(intr_table);
                                  interruptions := s.(interruptions);
                                  kernel_mode := s.(kernel_mode);
                                  pc := s.(pc);
                                  code := s.(code);
                                  stack := s.(stack); 
                                  register := s.(register);
                                  first_free_page :=   s.(first_free_page); 
                                  data := init_zero ( cr3_save * page_size)  page_size  s.(data)  |}
                                            

 }}
init_process_page_table cr3_save  {{ P }}.
Proof.
 eapply bind_wp.
  + intro s. apply update_memory_wp.
  + simpl. eapply weaken.
    - apply get_wp.
    - intros.  simpl. assumption.
Qed.


(*
Fixpoint get_index_page (beq : nat -> nat -> bool) (l : list nat) (a : nat) : (nat * nat) := 
  match l with
  | [] => (0, 0)
  | b :: l' => if beq a (removePermission b) then (0 , getOffset b permission_size)   
              else (S (fst (get_index_page beq l' a)) , 0) 
  end.
*)
(*
Definition get_index_pte cr3 : M (unit+nat):= 
perform s := get in 
let page_table := sublist (cr3 *page_size) nb_pte s.(data)in
let index_pte := get_index beq_nat page_table 0 in 
if  le_dec nb_pte index_pte then ret (inl tt) else  ret (inr  index_pte) .

*)


Definition update_pte (pte index : nat)  := 
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
    first_free_page := s.(first_free_page);
    data :=    firstn (s.(cr3) * page_size)  s.(data) 
            ++ update_sublist index pte (sublist (s.(cr3) * page_size) nb_pte  s.(data))
            ++ skipn (s.(cr3) * page_size + nb_pte )  s.(data)
|}).
 
Lemma update_pte_wp (pte index : nat) (P : unit-> state-> Prop) :
{{fun s => P tt {|
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
    data := firstn (s.(cr3) * page_size)  s.(data) 
            ++ update_sublist index pte (sublist (s.(cr3) * page_size) nb_pte s.(data))
            ++ skipn (s.(cr3) * page_size + nb_pte )  s.(data) |} 
}}
update_pte pte index  {{ P }}.
Proof. 
eapply modify_wp.
Qed.



Definition update_free_pages_list ( page : nat) := 
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
    data :=    firstn (page * page_size)  s.(data) 
            ++ update_sublist 0 s.(first_free_page) (sublist (page * page_size) nb_pte  s.(data))
            ++ skipn (page * page_size + nb_pte )  s.(data)
|}).

 
Lemma update_free_pages_list_wp ( page : nat) (P : unit-> state-> Prop) : 
{{fun s => P tt {|
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
    data :=    firstn (page * page_size)  s.(data) 
            ++ update_sublist 0 s.(first_free_page) (sublist (page * page_size) nb_pte  s.(data))
            ++ skipn (page * page_size + nb_pte )  s.(data) |}
}}
update_free_pages_list page {{ P }}.
Proof.
apply modify_wp.
Qed.

Definition free_page_update_memory index_page page :=
update_pte 0 index_page ;; update_free_pages_list page.

(*Definition remove_pte' Vaddr :=
perform s := get in 
let index := getBase Vaddr offset_nb_bits in 
if lt_dec index nb_pte then 
   let pte := List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 in 
     if beq_nat (removePermission pte) 0 then ret tt
     else 
     free_page_update_memory index  (removePermission pte) ;; 
     update_first_free_page  (removePermission pte)
else ret tt.
*)

Definition get_pte index :=
perform s := get in 
let pte := (List.nth ((s.(cr3) * page_size) + index ) s.(data)  0 ) in 
if beq_nat (removePermission pte) 0 then ret (inl 0) else ret (inr tt).



Definition add_pte_aux(permission index_pte : nat):=
perform page := alloc_page in 
match page with 
|inl p => perform s := get in update_pte (new_pte p permission) index_pte 
|_ => ret tt 
end.



(*********************** simple remove pte ************* *)





Definition update_pte_0 (pte index : nat) : M (nat+unit) := 
perform s := get in 
if   lt_dec 0  (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ))   then 
  if
    lt_dec (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 )) nb_page then 
 put  {|
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
    data :=    firstn (s.(cr3) * page_size)  s.(data) 
            ++ update_sublist index pte (sublist (s.(cr3) * page_size) nb_pte  s.(data))
            ++ skipn (s.(cr3) * page_size + nb_pte )  s.(data)
|};; ret ( inl (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 )))
else ret (inr tt)
else ret (inr tt).
 
Lemma update_pte_0_wp ( pte index : nat) (P : (nat+unit)-> state-> Prop) :

{{fun s => (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) <> 0 /\
           removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) < nb_page /\ 

 P (inl (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ))  ) {|
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
    data := firstn (s.(cr3) * page_size)  s.(data) 
            ++ update_sublist index pte (sublist (s.(cr3) * page_size) nb_pte s.(data))
            ++ skipn (s.(cr3) * page_size + nb_pte )  s.(data) |})  \/ 
((removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) = 0 \/
       nb_page   <=  removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 )) /\ P(inr tt) s)
            
}}
update_pte_0 pte index  {{ P }}.
Proof.
unfold update_pte_0.
eapply bind_wp.
instantiate (1:= fun S s =>S = s /\ ( (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) <> 0 /\
           removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) < nb_page /\ 
 P (inl (removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ))  ) {|
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
    data := firstn (s.(cr3) * page_size)  s.(data) 
            ++ update_sublist index pte (sublist (s.(cr3) * page_size) nb_pte s.(data))
            ++ skipn (s.(cr3) * page_size + nb_pte )  s.(data) |})  \/ 
    ((removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) = 0 \/
       nb_page <=    removePermission (List.nth index (sublist (s.(cr3)*page_size) nb_pte s.(data)) 0 ) ) /\ P(inr tt) s))). 
intro s.
destruct(lt_dec 0
       (removePermission
          (List.nth index (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0))). 
- destruct (     lt_dec
       (removePermission
          (List.nth index (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0))
       nb_page).
  + intros. 
    eapply bind_wp.
     * intros. eapply weaken.
       eapply ret_wp.
       intros.
       pattern a ,s0.
       eassumption.
     * intros. eapply weaken. 
       eapply put_wp.
       intros.
       simpl.
       destruct H. subst. 
       intuition.
       contradict l. 
       intuition.
       contradict H. 
       intuition.
  + eapply weaken. 
    eapply ret_wp.
    intros. 
    destruct H. subst.
    intuition.
- eapply weaken. 
  eapply ret_wp. 
  intros.
  destruct H. 
  subst. simpl. intuition. 
  contradict H0.
  intuition.
- eapply weaken. 
  eapply get_wp.
  intuition. 
Qed.

Definition free_page_update_memory' index_page  :=
perform page := update_pte_0  0 index_page in
match page with 
|inl p =>  update_free_pages_list p ;; ret (inl p)
|inr tt => (ret (inr tt))
end.

Definition remove_pte Vaddr :=
let index := getBase Vaddr offset_nb_bits in 
if lt_dec index nb_pte then 
perform page := free_page_update_memory' index  in 
match page with 
|inl p =>  update_first_free_page p
|inr tt => (ret  tt)
end
else ret tt.

Definition remove_pte' Vaddr : M bool:=
let index := getBase Vaddr offset_nb_bits in 
if lt_dec index nb_pte then 
perform page := free_page_update_memory' index  in 
match page with 
|inl p =>  update_first_free_page p;; ret true
|inr tt => (ret  false)
end 
else ret false.

Definition add_pte ( permission index_pte : nat): M unit :=
if lt_dec permission 4 then  
if le_dec nb_pte index_pte then 
   ret tt 
else 
perform s := get in 
 perform pte :=  get_pte index_pte   in 
   match pte with 
    | inl _ => add_pte_aux permission index_pte
    | inr _ => perform res := remove_pte' (index_pte * (Nat.pow 2 offset_nb_bits)) in
               match res with 
               | true =>  add_pte_aux permission index_pte
               | false => ret tt 
               end
          
end
else ret tt.

