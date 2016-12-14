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

(** Isolation & consistent properties
    + Some definitions *)

Require Import List Arith NPeano Coq.Logic.JMeq Coq.Logic.Classical_Prop.
Import List.ListNotations .
Require Import Lib StateMonad HMonad MMU MemoryManager PageTableManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Definition isolation (data: list nat) (process_list : list process) : Prop := 
forall  p1 p2 pg1 , 
In p2 process_list -> 
In p1 process_list -> 
p1.(cr3_save) <> p2.(cr3_save)->  
In pg1 (process_used_pages data p1) ->
~ In pg1 (process_used_pages data p2).

Inductive not_cyclic_aux (data : list nat) (pos : nat) (seen : list nat) : Prop :=
| nc_end : pos >= nb_page -> not_cyclic_aux data pos seen
| nc_step: pos < nb_page  -> ~In pos seen ->
           not_cyclic_aux data (List.nth (pos * page_size) data nb_page) (pos::seen) ->
           not_cyclic_aux data pos seen.

Definition not_cyclic (s : state) : Prop := not_cyclic_aux s.(data) s.(first_free_page) nil.

Inductive really_free_aux (process_list : list process) (data : list nat) (pos : nat) : Prop :=
| rf_end : pos >= nb_page -> really_free_aux process_list data pos
| rf_step: pos < nb_page -> ~In pos (all_used_pages data process_list) ->
           really_free_aux process_list data (List.nth (pos * page_size) data nb_page) ->
           really_free_aux process_list data pos.

Inductive Not_free_aux (p : nat) (data : list nat) (pos : nat) : Prop :=
|isNot_free_end : pos >= nb_page -> Not_free_aux p data pos
|isNot_free_step : pos < nb_page -> p <> pos -> Not_free_aux  p data (List.nth (pos * page_size) data nb_page) ->
           Not_free_aux  p data pos.

Inductive Free_notZero_aux (data : list nat) (pos : nat) : Prop :=
|isNot_zero_end : pos >= nb_page -> Free_notZero_aux data pos
|isNot_zero_step : pos < nb_page -> pos <> 0 -> Free_notZero_aux data (List.nth (pos * page_size) data nb_page) ->
           Free_notZero_aux data pos.

Definition page_table_length_aux (process_list :list  process) (data : list nat)  := 
forall p , In p process_list -> p.(cr3_save) < nb_page (*(p.(cr3_save) * page_size + nb_pte ) <=  length data *).

Definition page_table_length (s : state ) := 
page_table_length_aux s.(process_list) s.(data).

Definition  Not_free (s:state) cr3  : Prop :=
Not_free_aux cr3 s.(data) s.(first_free_page).

Definition used_notZero (s : state) : Prop :=
forall pg1 p1,
 In p1 s.(process_list) ->  In pg1 (process_used_pages s.(data)  p1) -> pg1 <> 0 /\ pg1 < nb_page.
 

Definition  free_notZero (s:state)  : Prop :=
Free_notZero_aux s.(data) s.(first_free_page).

Definition page_notZero (s:state)  : Prop :=
used_notZero s  /\ free_notZero s.

Definition really_free (s:state) : Prop :=
  really_free_aux s.(process_list) s.(data) s.(first_free_page).

Definition memory_length (s : state) : Prop :=
page_size * nb_page <= length (s.(data)).
 
Definition noDuplic_processPages (s : state) : Prop :=
forall p : process, In p s.(process_list) -> NoDup (process_used_pages s.(data) p).
 
Definition currProcess_inProcessList (s: state) : Prop :=
exists p, In p s.(process_list) /\ p.(cr3_save) = s.(cr3).
Definition consistent (s : state) : Prop :=
 really_free s /\ not_cyclic s /\  memory_length s  /\ 
noDuplic_processPages s /\ page_notZero s /\ currProcess_inProcessList s.

Hint Constructors not_cyclic_aux really_free_aux .

Definition cr3_properties s cr3 : Prop := 
(* Not_free s cr3 /\*) In  cr3 (all_cr3 s.(process_list)) /\ cr3 < nb_page /\ cr3 <> 0.

 
 

