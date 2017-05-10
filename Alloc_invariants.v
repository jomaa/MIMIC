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

Require Import List Arith NPeano Coq.Logic.JMeq Coq.Logic.Classical_Prop Omega.
Import List.ListNotations .
Require Import Lib StateMonad HMonad MMU Properties PageTableManager MemoryManager LibOs .
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Definition PTE_not_mapped s index cr3 : Prop := 
exists permission , sublist (cr3 *page_size) nb_pte  s.(data) = 
firstn index (sublist (cr3 *page_size) nb_pte s.(data)) ++ 
[new_pte 0 permission ] ++ skipn (index + 1)(sublist (cr3 *page_size) nb_pte s.(data)).

Definition index_free_pte_prop s cr3 index: Prop :=
PTE_not_mapped s index cr3 /\ index < nb_pte .
 
Lemma alloc_page_invariant  : 
(** first_free_page est libre **)
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s }} 
 alloc_page 
{{fun page (s: state) => isolation s.(data) s.(process_list)  /\ consistent s /\ 
                         match page with 
                          | inl p => ~ In  p (all_used_pages s.(data) s.(process_list)) /\  Not_free s p /\ p < nb_page /\ p <> 0
                          | _     => True (** echec **)
                         end }}.
Proof.
eapply weaken; [apply alloc_page_wp | idtac].
simpl.
unfold consistent, not_cyclic, really_free.
intros s (H1 & H2 & H3). simpl.
destruct (le_lt_dec nb_page s.(first_free_page)) as [ H4 | H4 ].
- tauto.
- left.
  split; trivial.
  split; trivial.
  split.
  + destruct H2.  
    * simpl. contradict H. intuition.
    * simpl. split. assumption.
      destruct H3.
      split.
      { destruct H3.
	 + contradict H3. intuition.
	 + eapply not_cyclic_aux_sublist.
           - instantiate (1:= [s.(first_free_page)]). assumption.
           - auto with *. }
         {  unfold memory_length in * . simpl.
           destruct H5 as ( HData (*& HPTlen*) & Hdup & (HU & HF) & k & HcurrP).
           simpl in *. 
            try repeat split; trivial.
              + simpl in *. unfold used_notZero in *.
                   generalize (HU pg1 p1).
                   intros. 
                   destruct H6.
                     -  apply H7;trivial.                   
                        unfold process_used_pages.
                        simpl. left. assumption.
                     -  apply H7;trivial.                   
                        unfold process_used_pages.
                        simpl. right. assumption.
             + simpl in *. unfold used_notZero in *.
                   generalize (HU pg1 p1).
                   intros. apply H7;trivial. 
             + unfold free_notZero in *.
             simpl in *. inversion HF. 
             contradict H5. intuition.
             assumption.
             + unfold currProcess_inProcessList in *. simpl. exists k. assumption. 
              
           }
  + destruct H2. contradict H4. intuition.  intros. unfold Not_free. simpl. split.
    * assumption.
    * destruct H3.  inversion H3.  
          { contradict H5. intuition. } 
          {split.  clear H3. clear H4 H H0 H6.  inversion H8. constructor. assumption. clear H3.
            constructor 2.  assumption.  contradict H0.  rewrite <- H0. intuition.
          induction H2.
          + contradict H2. intuition.
          + inversion H4.  constructor.  assumption. constructor 2.
            - assumption.
            - inversion H8.
              * contradict H11. intuition.
              * clear  H8 H4 H10 H H7 H11 IHreally_free_aux. destruct H13. contradict H. intuition. 
                contradict H4. rewrite H4. intuition. 
            -  apply IHreally_free_aux; trivial.
               * inversion H8.
                 { contradict H11. intuition. }
                 {  apply not_cyclic_aux_sublist with [pos; s.(first_free_page)] . assumption. intuition. } 
              * clear H9 IHreally_free_aux . inversion H8. contradict H9. intuition.
                destruct H12. contradict H12. intuition. intuition.
             + split. assumption.
                unfold page_notZero in *.
                
                destruct H5 as (HData (*& HPTlen*) & HNdup & (HU & HF) & HCur).
                unfold free_notZero in *.  inversion HF.
                contradict H5. 
                intuition. 
                assumption. }  
 Qed.

Lemma alloc_page_invariant2 index cr3 : 
(** first_free_page est libre **)
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s /\ index_free_pte_prop  s cr3 index /\
 cr3_properties s cr3 }} 
 alloc_page 
{{fun page (s: state) => (isolation s.(data) s.(process_list)  /\ consistent s /\
                         match page with 
                          | inl p => ~ In  p (all_used_pages s.(data) s.(process_list)) /\  Not_free s p /\ p < nb_page /\ p <> 0
                          | _     => True (** echec **)
                         end) /\ index_free_pte_prop  s cr3 index /\ cr3_properties s cr3 }}.
Proof.
apply post_and.

- eapply weaken.
  + apply alloc_page_invariant.
  + simpl. tauto.

- eapply weaken. 
  + eapply alloc_page_wp.
  + intros.  simpl. 
    destruct (le_lt_dec nb_page s.(first_free_page)) as [ H4 | H4 ].
     * right. intuition. 
     * left.
       unfold cr3_properties , index_free_pte_prop in *.
 
       simpl in *. 
       intuition.
Qed.

Lemma alloc_page_invariant3 index permission : 
(** first_free_page est libre **)
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s /\ index_free_pte_prop  s s.(cr3) index /\ 
 permission < 4  }} 
 alloc_page 
{{fun page (s: state) => (isolation s.(data) s.(process_list)  /\ consistent s /\
                         match page with 
                          | inl p => ~ In  p (all_used_pages s.(data) s.(process_list)) /\  Not_free s p /\ p < nb_page /\ p <> 0
                          | _     => True (** echec **)
                         end) /\ index_free_pte_prop  s s.(cr3) index /\  permission <4 }}.
Proof.
apply post_and.

- eapply weaken.
  + apply alloc_page_invariant.
  + simpl. tauto.

- eapply weaken. 
  + eapply alloc_page_wp.
  + intros.  simpl. 
    destruct (le_lt_dec nb_page s.(first_free_page)) as [ H4 | H4 ].
     * right. intuition. 
     * left.
       unfold cr3_properties , index_free_pte_prop in *.
 
       simpl in *. 
       intuition.
Qed.

