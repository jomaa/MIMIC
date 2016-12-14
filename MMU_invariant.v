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

Require Import List Arith NPeano Coq.Logic.JMeq Coq.Logic.Classical_Prop Omega.
Import List.ListNotations .
Require Import Lib StateMonad HMonad MMU Alloc_invariants Properties LibOs 
PageTableManager MemoryManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Lemma  translate_invariant Vaddr:
{{ fun (s : state) => isolation s.(data) s.(process_list) /\ consistent s
}} 
  translate Vaddr 
{{ fun Paddr  (s : state) => isolation s.(data) s.(process_list) /\ consistent s /\
match Paddr with 
inl paddr =>
(exists page index : nat,
    In page (get_mapped_pte s.(cr3) s.(data)) /\
    paddr = (page * page_size) + index /\ index < page_size)
| inr _ => True
end }}.
Proof.
eapply weaken.
 + eapply translate_wp.
 + intros.
   unfold consistent in *. 
   fold page_size.
   destruct H as (HIso & HRFree & HNCyc & HData (*& HPTlen*) & HNDup  & 
   Hpage).
   intros.  
   case_eq (lt_dec Vaddr  (2 ^ (offset_nb_bits + base_virt_page__nb_bits))).
    - intros.
      left. try repeat eexists.
      * assumption.
      * destruct H.
        rewrite Nat.pow_add_r in l.
        assert (Vaddr / 2 ^ offset_nb_bits <(2 ^ base_virt_page__nb_bits)).
         { apply Nat.div_lt_upper_bound.
            + unfold offset_nb_bits.
              simpl. omega. 
            + assumption.
         }
         { unfold getBase .
           destruct Hpage as ((HU & HF) & Hcurp).
           unfold  currProcess_inProcessList in *.
           destruct Hcurp.
           assert(page_table_length_aux s.(process_list) s.(data)) as HPTlen.
           unfold page_table_length in *.
           unfold page_table_length_aux in *.
           intros. 
           apply pagetable_position with s;intuition.
           unfold page_notZero in *.
           intuition.
           
           generalize (HPTlen x).
           intros.
           (*destruct H0.*)
           fold page_size in *.
           rewrite H2 in H0.
           unfold memory_length in *.
           apply le_lt_or_eq_iff in HData.
           destruct HData as [HData | HData];
           rewrite <- HData.
            + replace (2 ^ base_virt_page__nb_bits) with page_size in *.
               - assert  (s.(cr3) * page_size + page_size <= page_size * nb_page).
                 * rewrite <- H2.
                   replace (x.(cr3_save) * page_size + page_size)
                   with (S x.(cr3_save) * page_size).
                   rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                   unfold page_size. simpl. omega.    
                   apply lt_le_S.
                   intuition. 
                   rewrite <-Nat.mul_succ_l. reflexivity.
                 * apply le_lt_plus with  page_size;trivial.
              - unfold page_size.
                unfold base_virt_page__nb_bits, offset_nb_bits.
                reflexivity.
            + assert  (s.(cr3) * page_size + page_size <= page_size * nb_page).
              rewrite <- H2.
              replace (x.(cr3_save) * page_size + page_size)
              with (S x.(cr3_save) * page_size).
              rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
              unfold page_size. simpl. omega.    
              apply lt_le_S.
              intuition. 
              rewrite <-Nat.mul_succ_l. reflexivity.
              apply le_lt_plus with  page_size;trivial. }
      * case_eq (bit_to_bool
        (getOffset
        (List.nth ((s.(cr3) * page_size) + getBase Vaddr offset_nb_bits) 
        s.(data) d) valid_bits)).
         { intros. left.
           split.
           trivial.
           try repeat eexists.
            +  case_eq (get_access_permission
              (getOffset (getBase
              (List.nth ((s.(cr3)  * page_size) + getBase Vaddr offset_nb_bits)
              s.(data) d) valid_bits) accesPermission_bits)).
               - intros.
                 left.
                 split.
                  * left.
                    trivial.
                  * intuition.         
                    exists (removePermission 
                    ( List.nth  ((s.(cr3) * page_size) + getBase Vaddr offset_nb_bits) 
                    s.(data) d )).
                    exists (getOffset Vaddr offset_nb_bits). 
                    split.
                    { set(index:= getBase Vaddr offset_nb_bits).
                      unfold get_mapped_pte. 
                      apply in_map_iff.
                      exists (List.nth (s.(cr3) * page_size + index) s.(data) d) .
                      split. reflexivity.
                      apply filter_In.
                      split.
                      apply nth_in_sublist.
                       + unfold memory_length in *.
                         rewrite <- HData.
                         replace nb_pte with page_size in *. 
                         unfold currProcess_inProcessList in *.
                         destruct H3 as ( x & Hx & Hxs). 
                         rewrite <- Hxs in *.
                         replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                         rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                         unfold page_size. simpl. omega.    
                         assert(page_table_length_aux s.(process_list) s.(data)) as HPTlen.
                         unfold page_table_length in *.
                         unfold page_table_length_aux in *.
                         intros. 
                         apply pagetable_position with s;intuition.
                         unfold page_notZero in *.
                         intuition.
                         generalize (HPTlen x).
                         intros.
                         apply lt_le_S. 
                         apply H3.  assumption.  
                         rewrite <-Nat.mul_succ_l. reflexivity.
                         unfold page_size , nb_pte.
                         simpl. omega.
                       
                       + replace nb_pte with page_size;trivial.
                         unfold nb_pte.
                         unfold index.
                         unfold getBase.
                         unfold base_virt_page__nb_bits, offset_nb_bits.
                         destruct H.
                         rewrite Nat.pow_add_r in l.
                         apply Nat.div_lt_upper_bound.
                          - unfold offset_nb_bits.
                            simpl. omega. 
                          - unfold page_size. 
                            intuition.
                       + unfold isMapped_pte. 
                         case_eq (
                         (removePermission (List.nth (s.(cr3) * page_size + index) s.(data) d))
                         ).
                          - intros.
                            case_eq (getOffset (List.nth (s.(cr3) * page_size + index) s.(data) d) valid_bits).
                            intros.
                            unfold bit_to_bool in H0.
                            apply beq_nat_true in H0.
                            unfold index in *.
                            rewrite H5 in H0.
                            contradict H0. omega.
                            intros. trivial.
                           
                          - intros. trivial.
                             }
                     { split.
                       + unfold removePermission.
                         unfold shift_add.
                         reflexivity.
                       + unfold getOffset.
                         simpl.
                         rewrite Nat.land_ones.
                         fold page_size.
                         unfold page_size.
                         unfold offset_nb_bits .
                         simpl (2 ^ 4).
                         apply Nat.mod_upper_bound.
                         omega. }
               - intros.
                 case_eq (s.(kernel_mode)).
                  * intros. 
                    left.
                    split.
                    right. reflexivity.
                    intuition.        
                    exists (removePermission 
                    ( List.nth  ((s.(cr3) * page_size) + getBase Vaddr offset_nb_bits) 
                    s.(data) d )).
                    exists (getOffset Vaddr offset_nb_bits). 
                    split.
                    { set(index:= getBase Vaddr offset_nb_bits).
                      unfold get_mapped_pte. 
                      apply in_map_iff.
                      exists (List.nth (s.(cr3) * page_size + index) s.(data) d) .
                      split. reflexivity.
                      apply filter_In.
                      split.          
                      apply nth_in_sublist.
                       +  unfold memory_length in *.
                         rewrite <- HData.
                         replace nb_pte with page_size in *. 
                         unfold currProcess_inProcessList in *.
                         destruct H4 as ( x & Hx & Hxs). 
                         rewrite <- Hxs in *.
                         replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                         rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                         unfold page_size. simpl. omega.    
                         assert(page_table_length_aux s.(process_list) s.(data)) as HPTlen.
                         unfold page_table_length in *.
                         unfold page_table_length_aux in *.
                         intros. 
                         apply pagetable_position with s;intuition.
                         unfold page_notZero in *.
                         intuition.
                         generalize (HPTlen x).
                         intros.
                         intros. apply lt_le_S. 
                         apply H4.  assumption.  
                         rewrite <-Nat.mul_succ_l. reflexivity.
                         unfold page_size , nb_pte.
                         simpl. omega.
                       + replace nb_pte with page_size;trivial.
                         unfold nb_pte.
                         unfold index.
                         unfold getBase.
                         unfold base_virt_page__nb_bits, offset_nb_bits.
                         destruct H.
                         rewrite Nat.pow_add_r in l.
                         apply Nat.div_lt_upper_bound.
                          - unfold offset_nb_bits.
                            simpl. omega. 
                          - unfold page_size. 
                            intuition.
                       + unfold isMapped_pte. 
                         case_eq (beq_nat (List.nth (s.(cr3) * page_size + index) s.(data) d) 0).
                          - intros.
                            apply beq_nat_true in H5.
                            unfold index in *.
                            set (page :=  List.nth (s.(cr3) * page_size + 
                            getBase Vaddr offset_nb_bits) s.(data) d) in *.
                            contradict H1. 
                            unfold get_access_permission.
                            apply Bool.not_false_iff_true. 
                            rewrite Nat.ltb_lt.
                            unfold getBase.
                            unfold valid_bits.
                            simpl ( 2 ^ 1).
                            unfold accesPermission_bits.
                            unfold getOffset. 
                            rewrite Nat.land_ones.
                            simpl (2 ^ 1).
                            fold page_size.
                            unfold not.
                            intros.
                            rewrite H5.  simpl. 
                            contradict H0.
                            rewrite H5. 
                            unfold bit_to_bool. 
                            apply Bool.not_true_iff_false.
                            unfold getOffset. 
                            simpl. trivial. 
                          - intros.
                            case_eq (
                            (removePermission (List.nth (s.(cr3) * page_size + index) s.(data) d))).
                            * intros.
                            case_eq (getOffset (List.nth (s.(cr3) * page_size + index) s.(data) d) valid_bits).
                            intros.
                            unfold bit_to_bool in H0.
                            apply beq_nat_true in H0.
                            unfold index in *.
                            rewrite H7 in H0.
                            contradict H0. omega.

                            intros. trivial.
                           
                      * intuition. }
                     { split.
                       + unfold removePermission.
                         unfold shift_add.
                         reflexivity.
                       + unfold getOffset.
                         simpl.
                         rewrite Nat.land_ones.
                         fold page_size.
                         unfold page_size.
                         unfold offset_nb_bits .
                         simpl (2 ^ 4).
                         apply Nat.mod_upper_bound.
                         omega. }
                * intros.
                  right. intuition. }
 { intros.
     right.
     intuition. }
 - intros. right. intuition.
Qed.