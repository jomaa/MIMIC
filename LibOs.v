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
Require Import Lib StateMonad HMonad MMU Properties 
 PageTableManager MemoryManager .
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Lemma in_sublist:  (** !! CAN BE GENERALIZED **) 
forall l1 l2 pg2 p2,
sublist (p2.(cr3_save) * page_size) nb_pte   l1 = sublist (p2.(cr3_save) * page_size) nb_pte l2 ->  
In pg2 (process_used_pages l2 p2) -> In pg2 (process_used_pages l1 p2).
Proof.
intros.  
unfold process_used_pages in*.
simpl.  
destruct H0.
 +left. assumption.
 + right. simpl in H0. unfold get_mapped_pte in *. rewrite H. assumption.
Qed.

Lemma not_in_sublist : (** !! CAN BE GENERALIZED **)
forall l1 l2 pg1 p2, 
sublist (p2.(cr3_save) * page_size) nb_pte  l1 = sublist (p2.(cr3_save) * page_size) nb_pte  l2 ->  
~ In pg1 (process_used_pages l2 p2) -> ~ In pg1 (process_used_pages l1 p2).
Proof.
intros.
unfold not. intros. contradict H0.
apply in_sublist with l1;trivial. symmetry. trivial.
Qed.

Lemma sublist_unchanged new_l :   
forall i j len l, length new_l = len -> len > 0 ->  nb_page * page_size <= length l ->   i < nb_page * page_size -> j <= nb_page * page_size-> 
( i + len <= j  \/ j + len <= i ) -> 
sublist i len l = sublist i len  (firstn j l ++ new_l ++ skipn (j + len) l).
Proof.
intros i j len data len_new_l len_gt_0 Hdata Hi Hj [posJ | posI]. 

 + set (l2 := new_l ++ skipn (j + len) data).  rewrite sublist_firstn. rewrite sublist_app_le.
   - unfold sublist.  simpl.  rewrite firstn_skipn. rewrite firstn_skipn.
     rewrite firstn_firstn. rewrite Min.min_l.  reflexivity. auto with *.  
   - simpl. 
     unfold sublist. 
     simpl. rewrite firstn_length.
     simpl. rewrite Min.min_l. assumption. rewrite <- Hdata. assumption. 
 + rewrite sublist_two_app.
   - unfold sublist.
     rewrite skipn_skipn.
     rewrite firstn_length. rewrite len_new_l. 
     rewrite Min.min_l.
      * rewrite Nat.add_sub_assoc.
        set (a := j+len). rewrite minus_plus. reflexivity.
        assumption.
      *  rewrite <- Hdata. assumption. 
   - rewrite app_length.  
     rewrite firstn_length.
     rewrite len_new_l.
     rewrite Min.min_l. auto with *. 
     rewrite <- Hdata. assumption.   
Qed. 

Lemma process_eq_dec (p1 p2 : process) : {p1.(cr3_save) = p2.(cr3_save)}+{p1.(cr3_save) <> p2.(cr3_save)}.
Proof.
repeat decide equality.
Qed.

Theorem process_eq_dec3 (p p1 p2 : process) : 
 p1.(cr3_save) <> p2.(cr3_save)  -> {p.(cr3_save) = p1.(cr3_save) } + 
  {p.(cr3_save) = p2.(cr3_save)  } + 
  {p.(cr3_save) <> p1.(cr3_save) /\ p.(cr3_save) <> p2.(cr3_save)} .
Proof.
intros. 
destruct(process_eq_dec p1 p).
 - left.  left.  intuition. 
 - destruct (process_eq_dec p p2). left. right.  assumption. 
   right. split.  intuition. assumption. 
Qed.

Lemma not_cyclic_aux_sublist data pos seen1 seen2 :
  not_cyclic_aux data pos seen2 -> incl seen1 seen2 -> not_cyclic_aux data pos seen1.
Proof.
intros H1 H2.
revert seen1 H2.
induction H1; auto with *.
Qed.

Lemma really_free_aux_sublist data  l1 l2 pos :
  really_free_aux l2 data pos  -> incl (all_used_pages data l1) (all_used_pages data l2) -> really_free_aux l1 data pos.
Proof.
intros H1 H2.
revert l1 H2.
induction H1; auto with *.
Qed.

Lemma pagetable_position s: 
forall p, used_notZero s ->  In p s.(process_list) -> p.(cr3_save) < nb_page.
Proof.
intros. 
unfold page_notZero in *. 
unfold used_notZero in *.
generalize (H  p.(cr3_save) p). 
intros HUd.
destruct HUd;intuition. 
unfold process_used_pages.
simpl. 
left. 
reflexivity.
Qed.
               