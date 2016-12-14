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
Require Import Lib StateMonad HMonad MMU Alloc_invariants 
Properties LibOs PageTableManager MemoryManager MMU_invariant Removepte_invariant.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Definition spread_props s index cr3 := 
index_free_pte_prop s cr3 index /\ In cr3 (all_cr3 s.(process_list)).

Lemma insert_pte_prop s pg1 pte p1 index : 
In pg1
       (process_used_pages
          (firstn (p1.(cr3_save) * page_size) s.(data) ++
           (firstn index
              (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++
            [pte] ++
            skipn (index + 1)
              (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) ++
           skipn (p1.(cr3_save) * page_size + nb_pte) s.(data)) p1) ->
In p1 s.(process_list) ->
memory_length s ->
page_table_length s ->
index_free_pte_prop s p1.(cr3_save) index ->  

(pg1 =   (removePermission pte) \/    In pg1 (process_used_pages s.(data) p1)).
Proof.
intros H HProcess HData HPTlen HIndex .
unfold index_free_pte_prop in *. 
destruct HIndex.
unfold process_used_pages in H. 
unfold get_mapped_pte in H.
rewrite app_assoc with nat (firstn index
                   (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) ([pte])
                   (skipn (index + 1)
                   (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) in H.
simpl in H. 
rewrite in_map_iff in H.  
unfold process_used_pages. 
simpl. 
destruct H.
 + right. left.  assumption.
 + destruct H. destruct H.  rewrite filter_In in H2.
   destruct H2.
  rewrite sublist_eq_two_app in H2.
  - rewrite sublist_app_le in H2.
     * set (sublist_cr3 := ((firstn index
           (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++ 
           [pte]) ++
           skipn (index + 1)
           (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
       rewrite sublist_ident in H2.
         { unfold sublist_cr3 in *.
          unfold PTE_not_mapped in *.
          destruct H0.
          
           apply in_insert_app  with nat
           (firstn index (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) 
           (skipn (index + 1) (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)))
           x pte (new_pte 0 x0) in H2. 
           destruct H2. 
         + left. subst. f_equal. 
         + right. right. 
           unfold get_mapped_pte.
           rewrite  in_map_iff.
           exists x. 
           split. 
            - assumption.
            - rewrite filter_In.
              split.
               * replace (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))
                  with (firstn index (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++
                      [new_pte 0 x0] ++  skipn (index + 1) (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))).
                 assumption.
                
                 
               * assumption. }
         { unfold sublist_cr3.
           rewrite app_length.
           rewrite app_length.
           rewrite skipn_length.
           rewrite firstn_length.
           rewrite sublist_length.
            + rewrite min_l;trivial.
              rewrite Nat.sub_add_distr.
              rewrite Nat.add_sub_assoc.
              replace (length [pte]) with 1;auto with *.
              intuition. intuition. 
           + unfold memory_length in HData.
             rewrite <- HData.
             replace nb_pte with page_size in *. 
             replace (p1.(cr3_save) * page_size + page_size) with (S p1.(cr3_save) * page_size).
             rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
             unfold page_size. simpl. omega.   
             unfold page_table_length in *. 
             unfold page_table_length_aux in *.
             generalize (HPTlen p1).
             intros. apply lt_le_S. 
             destruct H.  
             apply H4. assumption.  
             rewrite <-Nat.mul_succ_l. reflexivity.
             unfold page_size , nb_pte.
             simpl. omega. }
     * simpl. 
       rewrite app_length.
       rewrite app_length.
       rewrite skipn_length.
       rewrite firstn_length.
       rewrite sublist_length.
        { rewrite min_l;trivial.
          rewrite Nat.sub_add_distr.
          rewrite Nat.add_sub_assoc.
          replace (length [pte]) with 1;auto with *.
          intuition. intuition. }
        { unfold memory_length in HData.
          rewrite <- HData.
          replace nb_pte with page_size in *. 
          replace (p1.(cr3_save) * page_size + page_size) with (S p1.(cr3_save) * page_size).
          rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
          unfold page_size. simpl. omega.   
          unfold page_table_length in *. 
          unfold page_table_length_aux in *.
          generalize (HPTlen p1).
          intros. apply lt_le_S. 
          destruct H.  
          apply H4. assumption.  
          rewrite <-Nat.mul_succ_l. reflexivity.
          unfold page_size , nb_pte.
          simpl. omega. }
  - rewrite firstn_length.
    apply min_l.
    unfold page_table_length in *.
    unfold  page_table_length_aux in *.
    generalize (HPTlen p1).
    intros. 
    unfold memory_length in *. 
    rewrite <- HData.
    intuition.
    rewrite mult_comm. apply mult_le_compat_l; trivial.  intuition.
    
Qed. 


Lemma insert_pte_length s cr3 index pte:
cr3 < nb_page -> 
memory_length s -> 
index_free_pte_prop s cr3 index -> length (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
               [pte] ++
               skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data)))= page_size.
Proof. 
intros HCr3 HData HIndex.
rewrite app_length.
rewrite app_length.
rewrite skipn_length.
rewrite firstn_length.
rewrite sublist_length.
 + rewrite min_l;trivial.
    - rewrite Nat.sub_add_distr.
      replace (length [pte]) with 1.
       * rewrite plus_assoc.
         replace nb_pte with page_size.
          { auto with *. rewrite <- Nat.sub_add_distr.
            rewrite Nat.add_sub_assoc.
             + rewrite minus_plus.  reflexivity.
             + unfold index_free_pte_prop in *. 
               destruct HIndex. 
               intuition. unfold memory_length in HData. 
               unfold page_size, nb_pte in *.
               simpl. 
               unfold nb_page in *. simpl in *. 
               omega. }
         { unfold memory_length in HData. 
           unfold page_size, nb_pte in *.
           simpl. unfold nb_page in *.
           simpl in *. 
           intuition. }
      * intuition. 
         - unfold index_free_pte_prop in *. 
           destruct HIndex. 
           intuition. 
 + unfold memory_length in HData. 
   unfold page_size, nb_pte in *.
   simpl. 
   unfold nb_page in *. simpl in *. 
   omega. 
Qed.

 
Lemma insert_pte_nth s cr3 index pte : 
forall ffp,  (ffp * page_size )<  (cr3 * page_size) \/  (cr3 * page_size) + page_size  <= (ffp * page_size )->
 memory_length s -> cr3 < nb_page ->
  index_free_pte_prop s cr3 index -> 
(List.nth (ffp * page_size) s.(data) nb_page) = (List.nth (ffp * page_size)
     (firstn (cr3 * page_size) s.(data) ++
   (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
    [pte] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data))) ++
   skipn (cr3 * page_size + nb_pte) s.(data)) nb_page).
Proof. 
intros ffp  H HData Hcr3 HIndex.
destruct H.
 + set (l1 := (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
    [pte] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data))) ++
   skipn (cr3 * page_size + nb_pte) s.(data)). 
   rewrite app_nth1. rewrite firstn_nth.  reflexivity.  assumption. 
   rewrite length_firstn_le. assumption.
   unfold memory_length in *. rewrite <- HData. rewrite mult_comm with page_size nb_page.
   apply mult_le_compat_r. intuition.

 + rewrite app_assoc.
   set(cr3_sublist := firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
   [pte] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data))).
   set (l1 := (firstn (cr3 * page_size) s.(data) ++ cr3_sublist)). 
   rewrite app_nth2.
    - rewrite skipn_nth.
      unfold l1.
      rewrite app_length. rewrite length_firstn_le.
       *  replace (length cr3_sublist) with page_size.
          rewrite Nat.add_sub_assoc.
          rewrite minus_plus. reflexivity.
            { assumption. }
            {  rewrite <- insert_pte_length with s cr3 index pte;intuition. }

       * unfold memory_length in *. rewrite <- HData. rewrite mult_comm with page_size nb_page.
         apply mult_le_compat_r. intuition.
    - unfold  l1. rewrite app_length.
      rewrite length_firstn_le.
       * replace (length cr3_sublist) with page_size.
         auto with *. rewrite <- insert_pte_length with s cr3 index pte;intuition.
       * unfold memory_length in *. rewrite <- HData. rewrite mult_comm with page_size nb_page.
         apply mult_le_compat_r. intuition. 
Qed.

Lemma really_free_insert_pte_prop s cr3 index pte:
In cr3 (all_cr3 s.(process_list)) ->
page_table_length s -> 
memory_length s ->
Not_free s (removePermission pte) ->
index_free_pte_prop s cr3 index ->
  really_free_aux s.(process_list) s.(data)  s.(first_free_page)->
  really_free_aux s.(process_list) 
                  (firstn (cr3 * page_size) s.(data) ++
                  (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
                  [pte] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data))) ++
                  skipn (cr3 * page_size + nb_pte) s.(data))
                  s.(first_free_page).
Proof.

intros Hcr3 HPTlen Hdata HNFree HIndex HRFree .
unfold all_cr3 in *.
rewrite in_map_iff in Hcr3.
unfold get_cr3 in *.
destruct Hcr3 as ( p & H & H2).
unfold page_table_length in *. unfold page_table_length_aux in *.
generalize ( HPTlen p ).
intro HPTlength.
inversion HNFree as [H3 | H3  HNFreepte not_free]. 
 + constructor. assumption. 
 + induction HRFree as [ffp HRfree | ffp HRfree H6 really_free]. 
      - contradict H. intuition.  
      - constructor 2.
        * assumption.
        * set (cr3_sublist := (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
               [pte] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data)))) in *. 
          clear IHreally_free really_free not_free HNFree.
          unfold all_used_pages in *. rewrite in_flat_map in *.
          unfold not in *. intros H7. apply H6. destruct H7 as (p1 & H7 & H8).
          clear H6.
          unfold cr3_sublist in *.  clear cr3_sublist. subst.
          destruct (process_eq_dec p p1).
           { subst. replace (p.(cr3_save)) with p1.(cr3_save) in *. clear e. 
             exists p1. split. assumption.
             apply insert_pte_prop with s ffp pte p1 index in H8;intuition.
              contradict H. intuition. 
            }
           { exists p1. 
             split. assumption.
             apply in_sublist with (firstn (p.(cr3_save) * page_size) s.(data) ++
             (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
             [pte] ++
             skipn (index + 1)
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) ++
             skipn (p.(cr3_save) * page_size + nb_pte) s.(data)).
             set (p_sublist := (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
             [pte] ++
             skipn (index + 1)
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p1.(cr3_save) * page_size) (p.(cr3_save) * page_size)  nb_pte s.(data).
               - reflexivity. 
               - unfold index_free_pte_prop in HIndex.
                 destruct HIndex as (HIndex0 & HIndex). 
                 unfold p_sublist.
                 rewrite app_length.
                 rewrite app_length.
                 rewrite skipn_length.
                 rewrite firstn_length.
                 rewrite sublist_length.
                 Focus 2. 
                 unfold memory_length in Hdata.
                 rewrite <- Hdata.
                 replace nb_pte with page_size in *. 
                 replace (p.(cr3_save) * page_size + page_size)
                 with (S p.(cr3_save) * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.    
                 generalize (HPTlen p ).
                 intros. apply lt_le_S. 
                 apply H. assumption.  
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite min_l;trivial.
                 rewrite Nat.sub_add_distr.
                 rewrite Nat.add_sub_assoc.
                 rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
                 replace (length [pte]) with 1;auto with *.
                 intuition. intuition. intuition. 
               - unfold nb_pte. simpl.  omega. 
               - intuition. 
               - generalize (HPTlen p1). intros. apply mult_lt_compat_r.
                  * apply H. assumption.
                  * unfold page_size.  simpl. omega.
               - generalize (HPTlen p). intros.  
                 apply mult_le_compat_r. intuition.  
               - apply NNPP.   unfold not in *.
                 intros H9.
                 apply n.
                 subst. 
                 apply not_or_and in H9.
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10. unfold page_size in H9.
                 unfold page_size in H10.
                 unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9.
                 simpl in H10 ,H9. 
                 apply not_le in H9. 
                 apply and_gt_plus. split; omega. 
               - assumption. }
            * inversion not_free. constructor. 
              rewrite <- insert_pte_nth with s cr3 index pte ffp;intuition.
               {apply not_eq_and_le_lt ;trivial.
                 subst. unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition. 
                 unfold page_size. simpl. omega. } 
               { rewrite insert_pte_nth   with s cr3 index pte ffp in IHreally_free.
                 apply IHreally_free;trivial.
                 
                  + clear IHreally_free.  rewrite <- insert_pte_nth;intuition. apply not_eq_and_le_lt;trivial.
                    subst. unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition.                    unfold page_size. simpl. omega.  
                  +  clear IHreally_free.  rewrite <- insert_pte_nth;intuition.
                    apply not_eq_and_le_lt;trivial.
                   subst. unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition. 
                    unfold page_size. simpl. omega.
                  +  clear IHreally_free.  inversion H4. constructor.
                     - rewrite <- insert_pte_nth;intuition.
                       apply not_eq_and_le_lt;trivial.
                       subst. unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition.
                       unfold page_size. simpl. omega.
                     - rewrite <- insert_pte_nth;intuition.
                       apply not_eq_and_le_lt;trivial.
                       subst. unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition.
                       unfold page_size. simpl. omega. 
                  +  clear IHreally_free.  apply not_eq_and_le_lt;trivial.
                    subst.  unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition.
                    unfold page_size. simpl. omega.  
                  + clear IHreally_free.  assumption. 
                  + clear IHreally_free.  subst. apply HPTlen. assumption.
                  +  clear IHreally_free.  assumption. }
Qed. 


Lemma insert_zero_prop2 s p pg index pte: 
In pg
       (get_mapped_pte p.(cr3_save)
          (firstn (p.(cr3_save) * page_size) s.(data) ++
           update_sublist index pte
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
           skipn (p.(cr3_save) * page_size + nb_pte) s.(data))) ->
In p s.(process_list) ->
memory_length s ->
page_table_length s ->
index < nb_pte -> 
PTE_not_mapped s index p.(cr3_save) ->
(pg = removePermission pte)\/ In pg (get_mapped_pte p.(cr3_save) s.(data)).


Proof.
intros H HProcess HData HPTlen HIndex HAP .
unfold get_mapped_pte in *. 
apply in_map_iff in H. 
destruct H. destruct H as (H & H2) .  rewrite filter_In in H2.
   destruct H2 as (H2 & H0).
  rewrite sublist_eq_two_app in H2.
  - rewrite sublist_app_le in H2.
     *unfold update_sublist in *.
       set (sublist_cr3 := (firstn index
           (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++ 
           [pte] ++
           skipn (index + 1)
           (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
       rewrite sublist_ident in H2.
         { unfold sublist_cr3 in *.
         rewrite app_assoc in H2.
         unfold PTE_not_mapped in *. 
         destruct HAP. 
         apply in_insert_app  with nat
           (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) 
           (skipn (index + 1) (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))
           x pte (new_pte 0 x0) in H2. 
           destruct H2. 
         + left. subst. reflexivity.  
         + right.
           rewrite  in_map_iff.
           exists x. 
           split. 
            - assumption.
            - rewrite filter_In.
              split.
               * replace (sublist (p.(cr3_save) * page_size) nb_pte s.(data))
                  with (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
                      [new_pte 0 x0] ++  skipn (index + 1) (sublist (p.(cr3_save) * page_size) nb_pte s.(data))).
                 assumption.
               * assumption. }
         { unfold sublist_cr3.
           rewrite app_length.
           rewrite app_length.
           rewrite skipn_length.
           rewrite firstn_length.
           rewrite sublist_length.
            + rewrite min_l;trivial.
              rewrite Nat.sub_add_distr.
              rewrite Nat.add_sub_assoc.
              replace (length [pte]) with 1;auto with *.
              intuition. intuition. 
           + unfold memory_length in HData.
             rewrite <- HData.
             replace nb_pte with page_size in *. 
             replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
             rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
             unfold page_size. simpl. omega.   
             unfold page_table_length in *. 
             unfold page_table_length_aux in *.
             generalize (HPTlen p).
             intros. apply lt_le_S. 
             destruct H.  
             apply H1. assumption.  
             rewrite <-Nat.mul_succ_l. reflexivity.
             unfold page_size , nb_pte.
             simpl. omega. }
     * simpl. 
       unfold update_sublist. 
       rewrite app_length.
       rewrite app_length.
       rewrite skipn_length.
       rewrite firstn_length.
       rewrite sublist_length.
        { rewrite min_l;trivial.
          rewrite Nat.sub_add_distr.
          rewrite Nat.add_sub_assoc.
          replace (length [pte]) with 1;auto with *.
          intuition. intuition. }
        { unfold memory_length in HData.
          rewrite <- HData.
          replace nb_pte with page_size in *. 
          replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
          rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
          unfold page_size. simpl. omega.   
          unfold page_table_length in *. 
          unfold page_table_length_aux in *.
          generalize (HPTlen p).
          intros. apply lt_le_S. 
          destruct H.  
          apply H1. assumption.  
          rewrite <-Nat.mul_succ_l. reflexivity.
          unfold page_size , nb_pte.
          simpl. omega. }
  - rewrite firstn_length.
    apply min_l.
    unfold page_table_length in *.
    unfold  page_table_length_aux in *.
    generalize (HPTlen p).
    intros. 
    unfold memory_length in *. 
    rewrite <- HData.
    intuition.
    rewrite mult_comm. apply mult_le_compat_l; trivial.  intuition.
    
Qed.
Lemma firstn_In (A : Type):
forall l i, forall a : A, In a (firstn i l) -> In a l.
Proof. 
intros.
rewrite <- List.firstn_skipn with A i l.
apply in_or_app.
left.
assumption.
Qed.
Lemma skipn_In (A : Type):
forall l i, forall a : A, In a (skipn (i+1) l) -> In a l.
Proof. 
intros.
rewrite <- List.firstn_skipn with A (i+1) l.
apply in_or_app.
right.
assumption.
Qed. 
   
    
Lemma free_not_zero_prop s pte index pos x:
memory_length s ->
 index_free_pte_prop s x.(cr3_save) index ->
In x s.(process_list) ->
x.(cr3_save) < nb_page ->
really_free_aux s.(process_list) s.(data) pos -> 
removePermission pte <> 0 -> (*In page (get_mapped_pte x.(cr3_save) s.(data)) ->*)
x.(cr3_save) <> pos ->

index < nb_pte -> 
Free_notZero_aux s.(data) pos -> 
Free_notZero_aux
  (firstn (x.(cr3_save) * page_size) s.(data) ++
   update_sublist index pte (sublist (x.(cr3_save) * page_size) page_size s.(data)) ++
   skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) pos.
Proof. 
intros HData HIndexpte Hx Hxcr3 HRFree Hpte Hposx HIndex HFNzero.
 inversion HRFree. 
  + constructor. 
    intuition. 
  + (*assert(pos <> page). 
    - unfold not in *.
      intros. 
      apply H0.
      unfold all_used_pages.
      apply in_flat_map. 
      exists x.
      split;trivial.
      rewrite H2.
      unfold process_used_pages. 
      simpl. right.
      assumption.
    - *) induction HFNzero.
      * constructor. assumption.
      * constructor 2;trivial.
        unfold update_sublist in *.
        rewrite <- insert_pte_nth;trivial.
        { inversion H1. 
          constructor. trivial.
          apply IHHFNzero;trivial. 
          inversion HFNzero.  contradict H7. intuition. 
          unfold not in *. intros. apply H5. 
          apply in_flat_map. 
          exists x.
          split;trivial.
          rewrite <- H10.
          unfold process_used_pages. 
          simpl. left. reflexivity.  }
        { apply not_eq_and_le_lt;trivial. intuition. 
          unfold page_size. simpl.
          omega. }
Qed.
      
Lemma  update_pte_invariant_add pte index :
{{ fun (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\ 
    ~ In (removePermission pte) (all_used_pages s.(data) s.(process_list)) /\
    Not_free s (removePermission pte) /\  (removePermission pte) < nb_page 
    /\ (removePermission pte) <> 0 /\

    index_free_pte_prop s s.(cr3) index }} 
  update_pte pte index 
 {{ fun _  (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s
      }}.
Proof.
eapply weaken.
 + eapply update_pte_wp.
 + intros. unfold consistent in *. simpl. 
  destruct H as (HIso &(HRFree & HNCyc & HData & (*HPTlen &*) HNdup & (HU & HF) & Hcurp ) & HUse & HNFree &  Hv1 & Hv2 & HIndex).
   simpl.  try repeat split.
    - unfold isolation in *.
      intros p1 p2 pg1 H2 H3 H4 H5.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      rewrite <- Hxs in *.
      unfold update_sublist in *. 
      set (l1 := firstn (s.(cr3) * page_size) s.(data) ) in *. 
      set (l2 := skipn (s.(cr3) * page_size + nb_pte) s.(data)) in *.
      set (l3 := (sublist (s.(cr3) * page_size) nb_pte s.(data))) in *.
      destruct (process_eq_dec3 x p1 p2) as [H7 | H7].
       * assumption. 
       * destruct H7 as [Hxp1 |Hxp2]. 
          { apply not_in_sublist with s.(data).
             +
               unfold l3. 
               set (cr3_sublist := (firstn index (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
               [pte] ++ skipn (index + 1) (sublist (s.(cr3) * page_size) nb_pte s.(data)))). 
               rewrite sublist_unchanged with  
               cr3_sublist 
               (p2.(cr3_save) * page_size) (s.(cr3) * page_size)  nb_pte s.(data).
                - unfold l1. unfold l2. unfold  cr3_sublist .   rewrite <- Hxs in *. reflexivity. 
                - unfold index_free_pte_prop in HIndex.
                  destruct HIndex as (HIndex0 & HIndex). 
                  unfold cr3_sublist.
                  rewrite app_length.
                  rewrite app_length.
                  rewrite skipn_length.
                  rewrite firstn_length.
                  rewrite sublist_length.
                  Focus 2. 
                  unfold memory_length in HData.
                  rewrite <- HData.
                  replace nb_pte with page_size in *. 
                  replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
                  rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                  unfold page_size. simpl. omega.   
                  apply lt_le_S. 
                  rewrite <- Hxs in *.
                  unfold l1, l2 , l3 in *. 
                  apply pagetable_position with  s;intuition. 

         
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  rewrite Nat.sub_add_distr.
                  rewrite Nat.add_sub_assoc.
                  rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
                  replace (length [pte]) with 1; auto with *. 
                  intuition. intuition. intuition. 
                - unfold nb_pte. simpl.  omega. 
                - intuition. 
                - apply mult_lt_compat_r.
                   *  apply pagetable_position with s;intuition. 
                   * unfold page_size.  simpl. omega.
                -    rewrite <- Hxs in *.
                  apply mult_le_compat_r.
                  assert (x.(cr3_save) < nb_page). 
                  apply pagetable_position with s;intuition.
                  auto with *.   
                - rewrite <- Hxs in *.
                  apply NNPP.   unfold not in *.
                  intros H9.
                  apply H4. unfold l1, l2 , l3 in *.
                  subst. 
                  apply not_or_and in H9.
                  destruct H9 as (H9 & H10).  
                  apply not_le in H10. unfold page_size in H9.
                  unfold page_size in H10.
                  unfold nb_pte in *.  
                  unfold offset_nb_bits in H10.
                  unfold offset_nb_bits in H9.
                  simpl in H10 ,H9. 
                  apply not_le in H9. 
                  apply and_gt_plus. split; omega. 
          + (****** modifier PT1 => ne pas modifier les entr\u00e9es mapp\u00e9es dans PT1 *******)
            unfold l1 ,l2, l3 in *.
            subst. replace  (x.(cr3_save)) with p1.(cr3_save) in *.
            apply insert_pte_prop in H5;trivial.
            destruct H5.
             - unfold process_used_pages.  simpl. apply and_not_or.
               split.
                * subst. unfold all_used_pages in HUse. rewrite  in_flat_map in HUse.
                  unfold not. unfold not in HUse. intros.
                  apply HUse. exists p2. split.  assumption.                  
                  unfold process_used_pages. simpl. left. assumption.
                * unfold not in *. 
                  intros.
                  apply HUse.
                  unfold all_used_pages.
                  apply in_flat_map.
                  exists p2.
                  split. assumption. 
                  unfold process_used_pages. 
                  simpl. 
                  right.  subst. assumption. 
             - generalize (HIso p1 p2 pg1).  intros. apply H0;trivial.
             - unfold page_table_length. 
             unfold page_table_length_aux. 
             intros. 
             apply pagetable_position with s;intuition. 
             }
           { unfold not. 
             intros. 
             contradict H5. 
             apply not_in_sublist with s.(data).
              +
                unfold l3. 
                set (cr3_sublist := (firstn index (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                [pte] ++ skipn (index + 1) (sublist (s.(cr3) * page_size) nb_pte s.(data)))). 
                rewrite sublist_unchanged with  
                cr3_sublist 
                (p1.(cr3_save) * page_size) (s.(cr3) * page_size)  nb_pte s.(data).
                - unfold l1. unfold l2.  unfold cr3_sublist. rewrite <- Hxs in *.
                  reflexivity. 
                - unfold index_free_pte_prop in HIndex.
                  destruct HIndex as (HIndex0 & HIndex). 
                  unfold cr3_sublist.
                  rewrite app_length.
                  rewrite app_length.
                  rewrite skipn_length.
                  rewrite firstn_length.
                  rewrite sublist_length.
                  Focus 2. 
                  unfold memory_length in HData.
                  rewrite <- HData.
                  replace nb_pte with page_size in *. 
                  replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
                  rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                  unfold page_size. simpl. omega.    
                  apply lt_le_S.
                  rewrite <- Hxs in *.
                  apply pagetable_position with s;intuition. 
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  rewrite Nat.sub_add_distr.
                  rewrite Nat.add_sub_assoc.
                  rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
                  replace (length [pte]) with 1;auto with *.
                  intuition. intuition. intuition. 
                - unfold nb_pte. simpl.  omega. 
                - intuition. 
                - apply mult_lt_compat_r.
                   * apply pagetable_position with s;intuition. 
                  
                   * unfold page_size.  simpl. omega.
                - apply mult_le_compat_r. 
              
                  rewrite <- Hxs in *.
                  assert(x.(cr3_save)<nb_page).
                  apply pagetable_position with s;intuition.
                  auto with *. 
                - apply NNPP.   unfold not in *.
                  intros H9.
                  apply H4. unfold l1, l2 , l3 in *.
                  subst. 
                  apply not_or_and in H9.
                  destruct H9 as (H9 & H10).  
                  apply not_le in H10. unfold page_size in H9.
                  unfold page_size in H10.
                  unfold nb_pte in *.  
                  unfold offset_nb_bits in H10.
                  unfold offset_nb_bits in H9.
                  simpl in H10 ,H9. 
                  apply not_le in H9. 
                  apply and_gt_plus. split; omega. 
          + (****** modifier PT1 => ne pas modifier les entr\u00e9es mapp\u00e9es dans PT1 *******)
            unfold l1 ,l2, l3 in *. 
            subst. replace  (x.(cr3_save)) with p2.(cr3_save) in *.
            apply insert_pte_prop in H;trivial.
            destruct H.
             - unfold process_used_pages.  simpl. apply and_not_or.
               split.
                * subst. unfold all_used_pages in HUse. rewrite  in_flat_map in HUse.
                  unfold not. unfold not in HUse. intros.
                  apply HUse. exists p1. split.  assumption.                  
                  unfold process_used_pages. simpl. left. assumption.
                * unfold not in *. 
                  intros.
                  apply HUse.
                  unfold all_used_pages.
                  apply in_flat_map.
                  exists p1.
                  split. assumption. 
                  unfold process_used_pages. 
                  simpl. 
                  right.  subst. assumption.
              - generalize (HIso p2 p1 pg1).  intros. apply H0;trivial. intuition.
              - unfold page_table_length. 
                unfold page_table_length_aux.
                intros. 
                  apply pagetable_position with s;intuition. 
                }
            
     * apply not_in_sublist with  s.(data) .
        {
          unfold l3. 
          set (cr3_sublist := (firstn index
          (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
          [pte] ++
          skipn (index + 1)
          (sublist (x.(cr3_save) * page_size)  nb_pte s.(data)))). 
          rewrite sublist_unchanged with  
          cr3_sublist 
          (p2.(cr3_save) * page_size) (x.(cr3_save)* page_size)  nb_pte s.(data).
            + unfold l1. unfold l2.  reflexivity.
            + unfold index_free_pte_prop in HIndex.
              destruct HIndex as (HIndex0 & HIndex).
              unfold cr3_sublist.
              rewrite app_length.
              rewrite app_length.
              rewrite skipn_length.
              rewrite firstn_length.
              rewrite sublist_length.
              Focus 2. 
              unfold memory_length in HData.
              rewrite <- HData.
              replace nb_pte with page_size in *. 
              replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
              rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
              unfold page_size. simpl. omega.
              apply lt_le_S.
     
                  apply pagetable_position with s;intuition. 
                  
              rewrite <-Nat.mul_succ_l. reflexivity.
              unfold page_size , nb_pte.
              simpl. omega.
              rewrite min_l;trivial.
              rewrite Nat.sub_add_distr.
              rewrite Nat.add_sub_assoc.
              rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
              replace (length [pte]) with 1;auto with *.
              intuition.
              intuition. 
              intuition. 
            + unfold nb_pte. simpl. omega.
            + intuition.
            +  apply mult_lt_compat_r.
               - apply pagetable_position with s;intuition. 
           
               - unfold page_size.  simpl. omega.
            + 
              apply mult_le_compat_r.
              assert(x.(cr3_save) < nb_page). 
              apply pagetable_position with s;intuition. 
                unfold l1 in *. unfold l3 in *. unfold l2 in *.
              subst. intuition.
            + apply NNPP.   unfold not in *.
              intros H9.
              apply H4. unfold l1, l2 , l3 in *.
              subst. 
              apply not_or_and in H9.
              destruct H9 as (H9 & H10).  
              apply not_le in H10. unfold page_size in H9.
              unfold page_size in H10.
              unfold nb_pte in *.  
              unfold offset_nb_bits in H10.
              unfold offset_nb_bits in H9.
              simpl in H10 ,H9. 
              apply not_le in H9. 
              apply and_gt_plus. split; omega.  }
       { generalize (HIso p1 p2 pg1).  intros. apply H;trivial.    
         clear H.
         apply in_sublist with  (l1 ++ (firstn index l3 ++ [pte] ++ skipn (index + 1) l3) ++ l2).
          + unfold index_free_pte_prop in HIndex.
            destruct HIndex as (HIndex0 & HIndex). 
            unfold l3. 
            set (cr3_sublist := (firstn index
            (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
            [pte] ++
            skipn (index + 1)
            (sublist (s.(cr3) * page_size)  nb_pte s.(data)))). 
            rewrite sublist_unchanged with  
            cr3_sublist 
            (p1.(cr3_save) * page_size) (s.(cr3) * page_size)  nb_pte s.(data).
             - unfold l1. unfold l2.  reflexivity.
             - unfold cr3_sublist.
               rewrite app_length.
               rewrite app_length.
               rewrite skipn_length.
               rewrite firstn_length.
               rewrite sublist_length.
               Focus 2. 
               unfold memory_length in HData.
               rewrite <- HData.
               replace nb_pte with page_size in *. 
               replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
               rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
               unfold page_size. simpl. omega.    
               apply lt_le_S. 
               unfold l1, l2 , l3 in *. rewrite <- Hxs in *. 
               apply pagetable_position with s;intuition.  
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial.
               rewrite Nat.sub_add_distr.
               rewrite Nat.add_sub_assoc.
               rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
               replace (length [pte]) with 1;auto with *.
               intuition.
               intuition. 
               intuition.
             - unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. 
             - unfold memory_length in HData. intuition.
             - apply mult_lt_compat_r.
                * apply pagetable_position with s;intuition.
                * unfold page_size.  simpl. omega.
             - 
               apply mult_le_compat_r. unfold l1 in *. unfold l3 in *.
               rewrite <- Hxs in *. 
               assert(x.(cr3_save) < nb_page).  
               apply pagetable_position with s;intuition.
               auto with *. 
             - destruct H7 as (Hxp1 & Hxp2).
               apply NNPP.   unfold not in *. intros H9.
               apply Hxp2.
               apply not_or_and in H9.
               destruct H9 as (H9 & H10).  
               apply not_le in H10. unfold page_size in H9.
               unfold page_size in H10.  unfold nb_pte in *.  
               unfold offset_nb_bits in H10.
               unfold offset_nb_bits in H9. simpl in H10 ,H9. 
               apply not_le in H9. 
               apply and_gt_plus. split; omega. 
          + unfold l1 , l2 , l3 .       rewrite <- Hxs in *. assumption. }  
   - unfold really_free in *. simpl.
     apply  really_free_insert_pte_prop;intuition.
     unfold currProcess_inProcessList in *.
     destruct Hcurp as ( x & Hx & Hxs). 
     rewrite <- Hxs in *.
     unfold all_cr3. 
     apply in_map_iff.
     exists x.
     unfold get_cr3. 
     intuition. unfold page_table_length. 
     unfold page_table_length_aux.
     intros.
               apply pagetable_position with s;intuition. 
     
   - unfold not_cyclic in *. simpl in *. inversion HNFree.
      * constructor.  assumption.  
      * inversion HRFree.
         { contradict H2. intuition. }
         { induction HNCyc.
           + contradict H. intuition.
           + constructor 2; trivial. inversion H1.
             - constructor . 
               unfold update_sublist. rewrite <- insert_pte_nth;intuition.
               apply not_eq_and_le_lt;trivial.
                   * subst. unfold not.
                     unfold currProcess_inProcessList in *.
                     destruct Hcurp as ( x & Hx & Hxs). 
                     rewrite <- Hxs in *.
                     intro HPTlength.
                     subst. clear IHHNCyc. 
                     intros.
                     apply H3. 
                     unfold all_used_pages. 
                     rewrite in_flat_map. 
                     exists x. 
                     split. assumption.
                     unfold process_used_pages. 
                     simpl. 
                     left. reflexivity.  
                   * unfold page_size. simpl. omega.
                   * unfold currProcess_inProcessList in *.
                    destruct Hcurp as ( x & Hx & Hxs). 
                    rewrite <- Hxs in *. clear IHHNCyc.
                    unfold used_notZero in *. 
                    generalize (HU x.(cr3_save) x).
                    intros. 
                    destruct H8;trivial. 
                    unfold process_used_pages in *. 
                    simpl. 
                    intuition.
              - unfold update_sublist. rewrite <-insert_pte_nth;intuition.
                 *  unfold update_sublist in *.
                    apply H11.
                    inversion H4. 
                    contradict H7. intuition. 
                    apply H12. 
                    inversion H4. 
                    contradict H10. intuition. 
                    assumption.
                 * apply not_eq_and_le_lt;trivial.
                   subst.
                   unfold not.
                   unfold currProcess_inProcessList in *.
                   destruct Hcurp as ( x & Hx & Hxs). 
                   rewrite <- Hxs in *.
                 
                   unfold page_table_length in *. unfold page_table_length_aux in *.
                
                   intros.
                   apply H3. 
                   unfold all_used_pages. 
                   rewrite in_flat_map. 
                   exists x. 
                   split. assumption.
                   unfold process_used_pages. 
                   simpl. 
                   left. assumption. 
                   unfold page_size. simpl. omega.
                 *unfold currProcess_inProcessList in *.
                    destruct Hcurp as ( x & Hx & Hxs). 
                    rewrite <- Hxs in *.
                    unfold used_notZero in *. 
                    generalize (HU x.(cr3_save) x).
                    intros. 
                    destruct H10;trivial. 
                    unfold process_used_pages in *. 
                    simpl. 
                    intuition. }
  - unfold memory_length. simpl.
    unfold update_sublist. rewrite app_length.
    rewrite app_length.
    unfold currProcess_inProcessList in *.
    destruct Hcurp as ( x & Hx & Hxs). 
    rewrite <- Hxs in *.
    intuition. 
    unfold page_table_length in *.
    unfold page_table_length_aux in *.
    unfold get_cr3 in *.
    unfold memory_length in *. 
    rewrite insert_pte_length;intuition.
    rewrite firstn_length.     
    rewrite Min.min_l.
      * rewrite skipn_length.
        rewrite plus_assoc. 
        replace nb_pte with page_size. 
        rewrite <- le_plus_minus with (x.(cr3_save) * page_size + page_size) (length s.(data)).
        unfold memory_length in *. 
        rewrite HData. intuition. 
        unfold memory_length in *. 
        rewrite <- HData. intuition.   
        replace (x.(cr3_save)  * page_size + page_size) with (S x.(cr3_save) * page_size);trivial. 
          { rewrite  mult_comm with page_size nb_page.
            apply Nat.mul_le_mono_pos_r .
              + simpl. unfold page_size. unfold page_size. simpl. omega.
              + apply gt_le_S. intuition.

               apply pagetable_position with s;intuition. }
          { apply mult_succ_l. }
          { intuition. }
      * rewrite  <- HData.
        rewrite mult_comm.
        assert(x.(cr3_save) < nb_page). 
     
               apply pagetable_position with s;intuition. 
auto with *.
*
               apply pagetable_position with s;intuition. 
  - unfold noDuplic_processPages in *.
    unfold all_used_pages.
    simpl in *.
    intros.
    unfold currProcess_inProcessList in *.
    destruct Hcurp as ( x & Hx & Hxs). 
    rewrite <- Hxs in *.

    unfold page_notZero in *.
    destruct (process_eq_dec x p).
     * replace (x.(cr3_save)) with (p.(cr3_save)) in *. 
       generalize (HNdup p ).
       intros.
       assert(In p s.(process_list));trivial.
       apply H0 in H. 
       inversion H.
       constructor. 
        { unfold not in *. 
          intros.
          unfold index_free_pte_prop in *.
          destruct HIndex as ( HIndex & HAP). subst.
          apply insert_zero_prop2 in H6;trivial.
          destruct H6. 
          unfold process_used_pages in H. 
         
          unfold all_used_pages in *. 
          rewrite in_flat_map in HUse.
          apply HUse.
          exists p.
          split. assumption. 
          unfold process_used_pages. simpl. 
          left. 
          assumption.
          apply H4. assumption. unfold page_table_length. 
          unfold page_table_length_aux. 
          intros. 
               apply pagetable_position with s;intuition. }
        { assert (In p s.(process_list));trivial.
          apply H0 in H1. clear H4 H2 H3.
          unfold update_sublist.
             set(p_sublist := (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
              [pte] ++
              skipn (index + 1) (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))).
          unfold get_mapped_pte.
             assert ((sublist (p.(cr3_save) * page_size) nb_pte
               (firstn (p.(cr3_save) * page_size) s.(data) ++
               p_sublist ++ skipn (p.(cr3_save) * page_size + nb_pte) s.(data)))
               = p_sublist ).
               + rewrite sublist_eq_two_app.
                  - rewrite sublist_zero_app_eq.
                    reflexivity.
                    symmetry.
                    apply insert_pte_length;trivial.
                    unfold used_notZero in *. 
                    generalize (HU p.(cr3_save) p).
                    intros. 
                    destruct H2;trivial. 
                    unfold process_used_pages in *. 
                    simpl. 
                    intuition. 
                  - rewrite firstn_length.
                    rewrite Min.min_l.
                    reflexivity. 
                    unfold memory_length in *. rewrite  <- HData.
                    rewrite mult_comm.
                    assert(p.(cr3_save) < nb_page). 
                   
               apply pagetable_position with s;intuition. 
                         auto with * .
              + rewrite H2.   
                unfold p_sublist.         
                rewrite <- filter_app.
                rewrite <- filter_app.
                simpl.
                unfold get_mapped_pte in H5. 
                 - assert (exists pg ,
                   (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) = 
                   (firstn index
                   (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++ [pg] ++
                   skipn (index + 1)
                   (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))).
                    * eexists. 
                      rewrite <- List.firstn_skipn at 1.
                      instantiate (2 := index). 
                      rewrite skipn_hd at 1.
                       { instantiate (2:=0).
                         instantiate (1:= List.nth index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0).
                         Opaque skipn.
                         simpl. 
                         rewrite Nat.add_1_r.
                         reflexivity. } 
                       { rewrite sublist_length.
                         unfold index_free_pte_prop in *. 
                         intuition.
                         unfold memory_length in HData.
                         rewrite <- HData.
                         replace nb_pte with page_size in *.
                           + replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
                                 - rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                                   unfold page_size. simpl. omega.   
                                    intros. apply lt_le_S.
                                    
               apply pagetable_position with s;intuition. 
                                 - rewrite <-Nat.mul_succ_l. reflexivity.
                           + unfold page_size , nb_pte.
                                simpl. omega. }
                    * subst. destruct H3.
                      clear H2.
                      rewrite H3 in H5. 
                      rewrite <- filter_app in H5.
                      rewrite <- filter_app in H5.
                      rewrite map_app in H5. 
                      rewrite map_app in H5. 
                      rewrite map_app.
                      rewrite map_app.
                      simpl in H5. 
                      subst.
                      destruct (isMapped_pte x1).
                      simpl in H5.                          
                      apply NoDup_remove_1 in H5.
                      destruct (isMapped_pte pte).
                       { simpl. 
                         apply NoDup_add_app.
                          + unfold all_used_pages in HUse.
                            rewrite in_flat_map in HUse.
                            unfold not in *.
                            intros.
                            apply HUse.
                            exists p.
                            split. 
                            assumption. 
                            unfold process_used_pages.
                            simpl.
                            right.
                            unfold get_mapped_pte.
                            rewrite in_map_iff. 
                            rewrite in_map_iff in H2.
                            destruct H2.
                            destruct H2.
                            subst.
                            exists x2.
                            split. assumption.
                            rewrite filter_In.
                            rewrite filter_In in H4.
                            destruct H4.
                            split;trivial.  
                            apply firstn_In in H4. 
                            assumption.
                          + unfold all_used_pages in HUse.
                            rewrite in_flat_map in HUse.
                            unfold not in *.
                            intros.
                            apply HUse.
                            exists p.
                            split. 
                            assumption. 
                            unfold process_used_pages.
                            simpl.
                            right.
                            unfold get_mapped_pte.
                            rewrite in_map_iff. 
                            rewrite in_map_iff in H2.
                            destruct H2.
                            destruct H2.
                            subst.
                            exists x2.
                            split. assumption.
                            rewrite filter_In.
                            rewrite filter_In in H4.
                            destruct H4.
                            split;trivial.  
                            apply skipn_In in H4. 
                            assumption.
                          + assumption. } 
                       { simpl.   assumption. }
                       { destruct (isMapped_pte pte). 
                         simpl. apply NoDup_add_app.
                             + unfold all_used_pages in HUse.
                               rewrite in_flat_map in HUse.
                               unfold not in *.
                               intros.
                               apply HUse.
                               exists p.
                               split. 
                               assumption. 
                               unfold process_used_pages.
                               simpl.
                               right.
                               unfold get_mapped_pte.
                               rewrite in_map_iff. 
                               rewrite in_map_iff in H2.
                               destruct H2.
                               destruct H2.
                               subst.
                               exists x2.
                               split. assumption.
                               rewrite filter_In.
                               rewrite filter_In in H4.
                               destruct H4.
                               split;trivial.  
                               apply firstn_In in H4. 
                               assumption.
                             + unfold all_used_pages in HUse.
                               rewrite in_flat_map in HUse.
                               unfold not in *.
                               intros.
                               apply HUse.
                               exists p.
                               split. 
                               assumption. 
                               unfold process_used_pages.
                               simpl.
                               right.
                               unfold get_mapped_pte.
                               rewrite in_map_iff. 
                               rewrite in_map_iff in H2.
                               destruct H2.
                               destruct H2.
                               subst.
                               exists x2.
                               split. assumption.
                               rewrite filter_In.
                               rewrite filter_In in H4.
                               destruct H4.
                               split;trivial.  
                                apply skipn_In in H4. 
                               assumption.
                             + assumption. 
                             + assumption.
} }
    * unfold noDuplic_processPages in *.
       intros.  Opaque update_sublist process_used_pages . simpl in *.
       Transparent update_sublist process_used_pages.
       unfold process_used_pages in *.
       generalize (HNdup p).
       intros.
       assert (
       get_mapped_pte p.(cr3_save) s.(data) =
       get_mapped_pte p.(cr3_save)
       (firstn (x.(cr3_save) * page_size) s.(data) ++
       update_sublist index pte
       (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
       skipn (x.(cr3_save) * page_size + nb_pte) s.(data))).
       unfold get_mapped_pte .
       f_equal. f_equal.
       { unfold update_sublist.
         set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
             [pte] ++
             skipn (index + 1)
             (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
              + reflexivity.  
              + unfold p_sublist.
                rewrite app_length.
                rewrite app_length.
                rewrite skipn_length.
                rewrite firstn_length.
                rewrite sublist_length.
                Focus 2. 
                unfold memory_length in HData.
                rewrite <- HData.
                replace nb_pte with page_size in *. 
                replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                unfold page_size. simpl. omega.    
                apply lt_le_S.
                
               apply pagetable_position with s;intuition. 
                 rewrite <-Nat.mul_succ_l. reflexivity.
                unfold page_size , nb_pte.
                simpl. omega.
                unfold index_free_pte_prop in *.
                destruct HIndex.
                rewrite min_l;trivial.
                rewrite Nat.sub_add_distr.
                rewrite Nat.add_sub_assoc.
                rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
                replace (length [pte]) with 1;auto with *.
                intuition.
                intuition.
                intuition.  
              + unfold nb_pte. simpl.  omega. 
              + intuition.
              + apply mult_lt_compat_r.
                  * apply pagetable_position with s;intuition. 
                  * unfold page_size.  simpl. omega.
              + apply mult_le_compat_r.
                assert(x.(cr3_save) < nb_page). 
                
               apply pagetable_position with s;intuition. 
                   intuition.  
              + apply NNPP.   unfold not in *.
                intros H9.
                apply n.
                subst. 
                apply not_or_and in H9.
                destruct H9 as (H9 & H10).  
                apply not_le in H10. unfold page_size in H9.
                unfold page_size in H10.
                unfold nb_pte in *.  
                unfold offset_nb_bits in H10.
                unfold offset_nb_bits in H9.
                simpl in H10 ,H9. 
                apply not_le in H9. 
                apply and_gt_plus. split; omega.  }
                { rewrite H1 in H0. apply H0. assumption. }
              
  - simpl ( {|
          process_list := s.(process_list);
          current_process := s.(current_process);
          cr3 := s.(HMonad.cr3);
          code := s.(code);
          intr_table := s.(intr_table);
          interruptions := s.(interruptions);
          kernel_mode := s.(kernel_mode);
          pc := s.(pc);
          stack := s.(stack);
          register := s.(register);
          data := firstn (s.(cr3) * page_size) s.(data) ++
                  update_sublist index pte
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                  skipn (s.(cr3) * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *. simpl in H.
          unfold update_sublist in *.
          unfold  page_notZero in *.
          unfold currProcess_inProcessList in *.
          destruct Hcurp as ( x & Hx & Hxs). 
          rewrite <- Hxs in *.
          unfold used_notZero in *.
          generalize (HU pg1 p1).
          intros.
          destruct (process_eq_dec p1 x).
           *
             replace (x.(cr3_save)) with (p1.(cr3_save)) in *.
             unfold process_used_pages in *.
             apply in_app_or in H0.
             destruct H0.
             destruct H0. 
             subst pg1.
             unfold used_notZero in *.
             apply H1;intuition. 
             intuition.   
             apply insert_zero_prop2 in H0;trivial.
                          destruct H0.
             subst pg1. 
             assumption. 
             destruct H1.
             assumption.
             simpl.
             right. assumption. assumption.
       
             unfold  index_free_pte_prop in *.
             intuition.
             unfold  index_free_pte_prop in *.
             intuition. unfold page_table_length. 
             unfold page_table_length_aux. 
             intros.
               apply pagetable_position with s;intuition.
               unfold  index_free_pte_prop in *.
             intuition.  unfold  index_free_pte_prop in *.
             intuition.
                   
           * apply H1.  intuition. 
             unfold update_sublist in *.
             set (l1 := firstn (s.(cr3) * page_size) s.(data) ) in *. 
             set (l2 := skipn (s.(cr3) * page_size + nb_pte) s.(data)) in *.
             set (l3 := (sublist (s.(cr3) * page_size) nb_pte s.(data))) in *.
             apply in_sublist with  (l1 ++ (firstn index l3 ++ [pte] ++ skipn (index + 1) l3) ++ l2).
              { unfold index_free_pte_prop in HIndex.
                destruct HIndex as (HIndex0 & HIndex). 
                unfold l3. 
                set (cr3_sublist := (firstn index
                (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                [pte] ++
                skipn (index + 1)
                (sublist (s.(cr3) * page_size)  nb_pte s.(data)))). 
                rewrite sublist_unchanged with  
                cr3_sublist 
                (p1.(cr3_save) * page_size) (s.(cr3) * page_size)  nb_pte s.(data).
                  - unfold l1. unfold l2.  reflexivity.
                  - unfold cr3_sublist.
                    rewrite app_length.
                    rewrite app_length.
                    rewrite skipn_length.
                    rewrite firstn_length.
                    rewrite sublist_length.
                    Focus 2. 
                    unfold memory_length in HData.
                    rewrite <- HData.
                    replace nb_pte with page_size in *. 
                    replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
                    rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                    unfold page_size. simpl. omega.    
                     intros. apply lt_le_S.
                     
                    rewrite <- Hxs in *.
                    apply pagetable_position with s;intuition. 
                    rewrite <-Nat.mul_succ_l. reflexivity.
                    unfold page_size , nb_pte.
                    simpl. omega.
                    rewrite min_l;trivial.
                    rewrite Nat.sub_add_distr.
                    rewrite Nat.add_sub_assoc.
                    rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
                    replace (length [pte]) with 1;auto with *.
                    intuition.
                    intuition. 
                    intuition.
                  - unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. 
                  - unfold memory_length in HData. intuition.
                  - apply mult_lt_compat_r.
                     * apply pagetable_position with s;intuition. 
                     * unfold page_size.  simpl. omega.
                  - apply mult_le_compat_r. rewrite <- Hxs.
                    assert(x.(cr3_save) < nb_page).
                    apply pagetable_position with s;intuition.
                    intuition.
                  - apply NNPP.   unfold not in *. intros H9.
                    apply n.
                    apply not_or_and in H9.
                    destruct H9 as (H9 & H10).  
                    apply not_le in H10. unfold page_size in H9.
                    unfold page_size in H10.  unfold nb_pte in *.  
                    unfold offset_nb_bits in H10.
                    unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                    apply not_le in H9. 
                    apply and_gt_plus. split; omega. } 
               { unfold l1 , l2 , l3 in *. rewrite <- Hxs in *. assumption. }  
                    
      - simpl ( {|
          process_list := s.(process_list);
          current_process := s.(current_process);
          cr3 := s.(HMonad.cr3);
          code := s.(code);
          intr_table := s.(intr_table);
          interruptions := s.(interruptions);
          kernel_mode := s.(kernel_mode);
          pc := s.(pc);
          stack := s.(stack);
          register := s.(register);
          data := firstn (s.(cr3) * page_size) s.(data) ++
                  update_sublist index pte
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                  skipn (s.(cr3) * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *. 
        simpl in H.
        unfold update_sublist in *. 
        unfold  page_notZero in *.
        unfold currProcess_inProcessList in *.
        destruct Hcurp as ( x & Hx & Hxs). 
        rewrite <- Hxs in *.
        unfold used_notZero in *.
        generalize (HU pg1 p1).
        intros.
        destruct (process_eq_dec p1 x).
         * replace (x.(cr3_save)) with (p1.(cr3_save)) in *.
           unfold process_used_pages in *.
           apply in_app_or in H0.
           destruct H0.
           destruct H0. 
           subst pg1.
           apply H1;intuition. 
           contradict H0.
           apply insert_zero_prop2 in H0;trivial.
           destruct H0.
           subst pg1. 
           assumption. 
           apply H1;intuition.
           unfold page_table_length. 
           unfold page_table_length_aux.
           intros. apply pagetable_position with s;intuition. 
           
           unfold  index_free_pte_prop in *.
           intuition.
           unfold  index_free_pte_prop in *.
           intuition.
         * apply H1.  intuition. 
             unfold update_sublist in *.
             set (l1 := firstn (s.(cr3) * page_size) s.(data) ) in *. 
             set (l2 := skipn (s.(cr3) * page_size + nb_pte) s.(data)) in *.
             set (l3 := (sublist (s.(cr3) * page_size) nb_pte s.(data))) in *.
             apply in_sublist with  (l1 ++ (firstn index l3 ++ [pte] ++ skipn (index + 1) l3) ++ l2).
              { unfold index_free_pte_prop in HIndex.
                destruct HIndex as (HIndex0 & HIndex). 
                unfold l3. 
                set (cr3_sublist := (firstn index
                (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                [pte] ++
                skipn (index + 1)
                (sublist (s.(cr3) * page_size)  nb_pte s.(data)))). 
                rewrite sublist_unchanged with  
                cr3_sublist 
                (p1.(cr3_save) * page_size) (s.(cr3) * page_size)  nb_pte s.(data).
                  - unfold l1. unfold l2.  reflexivity.
                  - unfold cr3_sublist.
                    rewrite app_length.
                    rewrite app_length.
                    rewrite skipn_length.
                    rewrite firstn_length.
                    rewrite sublist_length.
                    Focus 2. 
                    unfold memory_length in HData.
                    rewrite <- HData.
                    replace nb_pte with page_size in *. 
                    replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
                    rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                    unfold page_size. simpl. omega.    
                   apply lt_le_S.
                    unfold l1, l2 , l3 in *.
                    rewrite <- Hxs in *.
                    
                   apply pagetable_position with s;intuition.
                   
                    rewrite <-Nat.mul_succ_l. reflexivity.
                    unfold page_size , nb_pte.
                    simpl. omega.
                    rewrite min_l;trivial.
                    rewrite Nat.sub_add_distr.
                    rewrite Nat.add_sub_assoc.
                    rewrite Nat.add_sub_assoc with (length [pte]) nb_pte index.
                    replace (length [pte]) with 1;auto with *.
                    intuition.
                    intuition. 
                    intuition.
                  - unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. 
                  - unfold memory_length in HData. intuition.
                  -  apply mult_lt_compat_r.
                     * apply pagetable_position with s;intuition.
                     * unfold page_size.  simpl. omega.
                  - apply mult_le_compat_r. unfold l1 in *.
                    unfold l3 in *. unfold l2 in *.
                    rewrite <- Hxs.
                    assert(x.(cr3_save) < nb_page).
                    
                    apply pagetable_position with s;intuition.
                    intuition.
                  - apply NNPP.   unfold not in *. intros H9.
                    apply n.
                    apply not_or_and in H9.
                    destruct H9 as (H9 & H10).  
                    apply not_le in H10. unfold page_size in H9.
                    unfold page_size in H10.  unfold nb_pte in *.  
                    unfold offset_nb_bits in H10.
                    unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                    apply not_le in H9. 
                    apply and_gt_plus. split; omega. } 
               { unfold l1 , l2 , l3 in *. rewrite <- Hxs in *. assumption. }  
  - unfold page_notZero in *. unfold free_notZero. 
    simpl.
    unfold free_notZero in *.
    unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      rewrite <- Hxs in *.
    apply free_not_zero_prop;trivial.
     * unfold used_notZero in *. 
       generalize (HU x.(cr3_save) x).
       intros. 
       destruct H;trivial. 
       unfold process_used_pages in *. 
       simpl. 
       intuition. 
     * assert (In x.(cr3_save) (all_used_pages s.(data) s.(process_list))).
       { unfold all_used_pages. 
         apply in_flat_map. 
         exists x.
         split;trivial.
         unfold process_used_pages. 
         simpl.
         left. reflexivity. }
       { inversion HRFree.
         unfold not in *.
         intros.
         contradict H0. rewrite <- H1.
         assert (x.(cr3_save) < nb_page).
         unfold used_notZero in *. 
       generalize (HU x.(cr3_save) x).
       intros. 
       destruct H0;trivial. 
       unfold process_used_pages in *. 
       simpl. 
       intuition. 
         
         intuition.
         unfold not in *. 
         intros. 
         apply H1.
         rewrite <- H3.
         assumption. }
     * unfold index_free_pte_prop in *. intuition.

  - assumption.
Qed.

Lemma get_pte_wp index (P : (nat+unit) -> state -> Prop): 
{{fun s => 

removePermission (List.nth ((s.(cr3) * page_size) + index ) s.(data)  0 )  = 0 /\ P (inl 0) s \/
removePermission (List.nth ((s.(cr3) * page_size) + index ) s.(data)  0 )  <> 0 /\ P (inr tt) s 
}}
get_pte index {{ P }}.
Proof.
unfold get_pte.

eapply bind_wp. 
 + intro s. 
   instantiate (1 := fun s s'=> s = s'  
/\ ((removePermission (List.nth ((s.(cr3) * page_size) + index ) s.(data)  0)   = 0 
 /\ P (inl 0) s)  \/ ( removePermission (List.nth ((s.(cr3) * page_size) + index ) s.(data)  0 )  <> 0 
/\ P (inr tt) s) ) ).
 
  case_eq (beq_nat (removePermission (List.nth (s.(cr3) * page_size + index) s.(data) 0)) 0).
 
- intros. eapply weaken.
      * eapply ret_wp.
      * intros. intuition.  subst. assumption.
      apply beq_nat_true in H. 
      intuition.
    -intros. eapply weaken.
      * eapply ret_wp.
      * intros. intuition. 
       subst. 
      apply beq_nat_false in H. 
      intuition. subst.
      assumption.
 + eapply weaken.
   - eapply get_wp.
   -  intros. simpl. intuition.
Qed.

Definition pte_is_mapped s index cr3  :=
 removePermission(List.nth ((cr3 * page_size) + index) s.(data) 0) <> 0 /\ 

removePermission (List.nth ((cr3 * page_size) + index) s.(data) 0 ) < nb_page.


Definition index_mapped_pte_prop s cr3 index :=
pte_is_mapped s index cr3 /\ index < nb_pte.

Lemma get_pte_invariant index : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s /\  index < nb_pte }}
 get_pte index 
{{ fun val (s :state) => isolation s.(data) s.(process_list)  /\ consistent s /\ 
                           match val with 
                           | inl  _=> index_free_pte_prop  s s.(cr3) index 
                           | inr _   =>  index_mapped_pte_prop s s.(cr3) index   
                           end }}.
Proof.
eapply weaken.
 + eapply get_pte_wp.
 + intros. simpl. 
   unfold index_free_pte_prop. 
   unfold PTE_not_mapped . 
   case_eq (beq_nat (removePermission (List.nth (s.(cr3) * page_size + index) s.(data) 0) ) 0 ). 
   intros. 
    - left.  intuition. apply beq_nat_true in H0.  assumption.
      set (b:=(List.nth (s.(cr3) * page_size + index) s.(data) 0)) in *.
      eexists . 
      apply exists_page_get_index_page_le;trivial.
       * apply sublist_length.
         unfold  memory_length in *.
         unfold consistent in *.
         intuition.
         replace nb_pte with page_size in *. 
         replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
         unfold memory_length in *. 
         rewrite <- H4.
         rewrite mult_comm.
         apply Nat.mul_le_mono_pos_l.
         unfold page_size. simpl. omega.
         unfold cr3_properties in *.
         apply lt_le_S. 
         unfold currProcess_inProcessList in *.
         destruct H8.
         destruct H7. 
         unfold page_notZero in *.
         destruct H6. 
         unfold used_notZero in *.
         generalize (H6 s.(cr3) x).
         intros.
         apply H10;trivial.
         unfold process_used_pages. 
         simpl. 
         left. assumption. 
         rewrite <-Nat.mul_succ_l. reflexivity.
         unfold page_size , nb_pte.
         simpl. omega.
       * instantiate (1:= (getOffset b permission_size)).
         apply beq_nat_true in H0.
         unfold b in H0. 
         rewrite add_remove_permission.
         unfold sublist. rewrite firstn_nth.
         rewrite skipn_nth. 
         intuition. assumption.     
   - intros. right. apply beq_nat_false in H0.  intuition.
     unfold index_mapped_pte_prop. 
     unfold pte_is_mapped . intuition.
     unfold consistent in *. 
     destruct H as (HRFree & HNCyc & HData (*& HPTlen*) & HNdup & (HF & HU) & Hcur).
     unfold cr3_properties in *.
     unfold currProcess_inProcessList in *.
     destruct Hcur.
     (*
     
     destruct H2 as (Hcr3 & HCr31 & Hcr32).
     unfold all_cr3 in *.
     apply in_map_iff in Hcr3.
     destruct Hcr3.
     unfold get_cr3 in *. 
     destruct H.
     rewrite <- H.*)
     unfold used_notZero in *. 
     generalize (HF (removePermission (List.nth (x.(cr3_save) * page_size + index) s.(data) 0)) x).
     intros. destruct H2. 
     intuition. 
     unfold process_used_pages. 
     simpl. 
     right. 
     set (a := removePermission (List.nth (x.(cr3_save) * page_size + index) s.(data) 0)) in *.
     unfold get_mapped_pte. 
     apply in_map_iff. 
     exists (List.nth (x.(cr3_save) * page_size + index) s.(data) 0).     
     split.
     unfold a. 
     reflexivity. 
     apply filter_In. 
     split.
     rewrite <- skipn_nth.
     rewrite <- firstn_nth with nat 0 index nb_pte (skipn (x.(cr3_save) * page_size) s.(data)).
     unfold sublist.
     apply  nth_In.
     rewrite firstn_length.
     rewrite skipn_length.
      rewrite min_l;trivial.
     unfold  memory_length in *.
     apply Nat.le_add_le_sub_r.
     rewrite <- HData.
     replace nb_pte with page_size;trivial.
     rewrite plus_comm at 1. 
     replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
     rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
     unfold page_size. simpl. omega.
     assert(x.(cr3_save) < nb_page).
     apply pagetable_position with s;intuition.
     
     intuition.    rewrite <-Nat.mul_succ_l. reflexivity.
     assumption.
     unfold isMapped_pte.
     case_eq ( beq_nat
      (removePermission
         (List.nth (x.(cr3_save) * page_size + index) s.(data) 0)) 0). 
     intros. 
     apply beq_nat_true in H2.
     contradict H2.
     destruct H. rewrite H2. intuition. 
     intros.
     case_eq(removePermission (List.nth (x.(cr3_save) * page_size + index) s.(data) 0)).
     intros. 
     apply beq_nat_false in H2.
     contradict H2. 
     assumption.
     intros.
     trivial.
     destruct H. rewrite <- H5. assumption.
Qed.

Lemma add_pte_aux_invariant permission index: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s /\ 
                  index_free_pte_prop s s.(cr3) index  /\  permission < 4
                  
}}
 add_pte_aux permission index
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s   }}.
Proof. 
unfold add_pte_aux.
* eapply bind_wp_rev.
  { apply alloc_page_invariant3. }
  { intros [ pg| [] ].
    intros.
    eapply bind_wp. 
    intro s. 
    eapply update_pte_invariant_add.
    eapply weaken. eapply get_wp. 
    intros. 
    simpl. 
    
    unfold consistent in *.
    destruct H as ((HIso & (HRFree & HNCyc & HData (*& HPTlen*) & HNdup & HNPzero) &  
    (HPte1 & HPte2 & HPte3)) & HNFree & Hpteval).
    unfold  page_notZero in *.
    destruct HNPzero as ((HU & HF) & Hcur).      
    unfold cr3_properties, index_free_pte_prop in *.
    unfold all_cr3. 
    unfold currProcess_inProcessList in *. 
    destruct Hcur as (p & Hp & Hps).
    try repeat split;  trivial.
     +  unfold used_notZero in *.
        generalize (HU pg1 p1). intros. 
        apply H1;intuition. 
     + unfold used_notZero in *.
       generalize (HU pg1 p1). intros. 
       apply H1;intuition. 
     +  exists p. 
        unfold get_cr3. 
        intuition.
     + rewrite  remove_add_permission;trivial. 
     + rewrite  remove_add_permission;trivial.
     + rewrite  remove_add_permission;trivial. intuition.  
     + rewrite  remove_add_permission;trivial.  intuition. 
     + intuition. 
     + intuition.
     + eapply weaken.  eapply ret_wp.
       intuition. }
Qed.


Lemma add_pte_invariant permission index: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s }}
 add_pte  permission index
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
unfold add_pte.
case (lt_dec permission 4).
intros Hperm.  
case_eq (le_dec nb_pte index). 
 - intros.
   eapply weaken. 
   apply ret_wp.
   intros.  simpl. intuition.
 - intros. simpl.
   eapply bind_wp_rev.
   eapply get_wp.
   intros.
   eapply bind_wp_rev.
   eapply weaken.
   eapply get_pte_invariant.
    + intros.
      simpl. intuition.
    + intros. destruct a0. 
       *  eapply weaken.  
         eapply add_pte_aux_invariant.
         intros.
         simpl.
         intuition.
       * eapply bind_wp_rev.
           { eapply weaken. 
             apply remove_pte_invariant'.
             intros. simpl.
             intuition. }
           { intros [] . eapply weaken. 
              eapply add_pte_aux_invariant.
                - intros.
                  simpl.
                  intuition.
                  unfold index_free_pte_prop.
                  split. 
                  * unfold PTE_not_mapped .
                    exists 0. 
                    unfold new_pte.
                    unfold shift_add.
                    simpl(0 * 2 ^ permission_size + 0).
                    apply exists_page_get_index_page_le;trivial.
                    (*unfold l3.*) 
                    apply sublist_length.
                    unfold  memory_length in *.
                  unfold consistent in *.
                  intuition.
                  replace nb_pte with page_size in *. 
                  replace (s.(cr3) * page_size + page_size) with (S s.(cr3) * page_size).
                  unfold memory_length in *. 
                  rewrite mult_comm.
                  rewrite <- H4.
                  apply Nat.mul_le_mono_pos_l.
                  unfold page_size. simpl. omega.
                  unfold currProcess_inProcessList in *.
                  destruct H8 as ( x & Hx & Hxs). 
                  rewrite <- Hxs in *.
                  unfold all_cr3. 
                  destruct H6 as (HU& HF). 
                  unfold used_notZero in *. 
                  generalize (HU x.(cr3_save) x).
                     intros. 
                     destruct H6;trivial. 
                     unfold process_used_pages in *. 
                     simpl. 
                     intuition.
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  simpl. intuition. intuition. 
                  
                 (* case_eq permission. intros. 
                  apply beq_nat_true in H0.
                  simpl.
*)                  unfold removePermission in *. 
                  unfold getBase in *. 
                  simpl ( 2 ^ offset_nb_bits) in *.
                 rewrite Nat.div_mul in H3.  intuition.
                  intuition.  
                  intuition. 
                  *  intuition.
              - intros. eapply weaken.  eapply ret_wp. 
              intuition.
              }
-intros. eapply weaken. eapply ret_wp. intuition. 


Qed. 
