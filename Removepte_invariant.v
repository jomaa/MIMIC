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
Require Import Lib StateMonad HMonad MMU Alloc_invariants
 Properties LibOs PageTableManager MemoryManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Lemma insert_zero_prop s pg1 p1 index : 
In pg1
       (process_used_pages
          (firstn (p1.(cr3_save) * page_size) s.(data) ++
           (firstn index
              (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++
            [0] ++
            skipn (index + 1)
              (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) ++
           skipn (p1.(cr3_save) * page_size + nb_pte) s.(data)) p1) ->
In p1 s.(process_list) ->
memory_length s ->
(forall p , In p s.(process_list) -> p.(cr3_save) < nb_page) ->
index < nb_pte -> 
(*pg1 <> 0 -> *)
In pg1 (process_used_pages s.(data) p1).
Proof.
intros H HProcess HData HPTlen HIndex (*HPageN0*) .
unfold process_used_pages in H. 
unfold get_mapped_pte in H.
rewrite app_assoc with nat (firstn index
                   (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) ([0])
                   (skipn (index + 1)
                   (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) in H.
simpl in H. 
rewrite in_map_iff in H.  
unfold process_used_pages. 
simpl. 
destruct H.
 + left.  assumption.
 + destruct H. destruct H as (H1 & H2).  rewrite filter_In in H2.
   destruct H2 as (H2 & H).
  rewrite sublist_eq_two_app in H2.
  - rewrite sublist_app_le in H2.
     * right.  unfold process_used_pages.     
       unfold get_mapped_pte.
       rewrite in_map_iff.
       exists x.
       split. assumption. 
       rewrite filter_In.
       split.
        { rewrite sublist_ident in H2.   
           + rewrite <-  List.firstn_skipn with  nat index (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)).
             subst.
             rewrite app_assoc_reverse in H2. 
             apply in_app_or in H2. apply in_or_app.
             destruct H2.
              - left. assumption. 
              - simpl in H0. 
                destruct H0.
                contradict H.
                unfold isMapped_pte.
                
                case_eq ( removePermission x ).
                intros.
                case_eq (getOffset x valid_bits).
                intros. intuition. 
                
                
                
                intros.
                unfold getOffset in H1.
                rewrite <- H0 in H1.
                rewrite Nat.land_0_l in H1.
                contradict H1. intuition. 
                intros. 
                rewrite <- H0 in H.
                unfold removePermission in H. 
                unfold getBase in *.
                unfold permission_size in *.
                simpl in H.
                contradict H.
                omega.
                
                
           
                right. 
                apply In_skipn. assumption. 
           + rewrite app_length.
             rewrite app_length.
             rewrite skipn_length.
             rewrite firstn_length.
             rewrite sublist_length.
              { rewrite min_l;trivial.
                rewrite Nat.sub_add_distr.
                rewrite Nat.add_sub_assoc.
                replace (length [0]) with 1;auto with *.
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
               apply H0. assumption.  
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega. } }
       {  assumption.  }
       
     * simpl. 
       rewrite app_length.
       rewrite app_length.
       rewrite skipn_length.
       rewrite firstn_length.
       rewrite sublist_length.
        { rewrite min_l;trivial.
          rewrite Nat.sub_add_distr.
          rewrite Nat.add_sub_assoc.
          replace (length [0]) with 1;auto with *.
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
          apply H0. assumption.  
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
index < nb_pte-> length (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
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
             + unfold memory_length in HData. 
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
           intuition. intuition.  
 + unfold memory_length in HData. 
   unfold page_size, nb_pte in *.
   simpl. 
   unfold nb_page in *. simpl in *. 
   omega. 
Qed.
Lemma insert_pte_nth s cr3 index pte : 
forall ffp,  (ffp * page_size )<  (cr3 * page_size) \/  (cr3 * page_size) + page_size  <= (ffp * page_size )->
 memory_length s -> cr3 < nb_page ->
 index < nb_pte -> 
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


Lemma really_free_insert_pteZero_prop s cr3 index:
In cr3 (all_cr3 s.(process_list)) ->
(forall p , In p s.(process_list) -> p.(cr3_save) < nb_page) -> 
memory_length s ->
used_notZero s ->
index < nb_pte ->
  really_free_aux s.(process_list) s.(data)  s.(first_free_page)->
  really_free_aux s.(process_list) 
                  (firstn (cr3 * page_size) s.(data) ++
                  (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
                  [0] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data))) ++
                  skipn (cr3 * page_size + nb_pte) s.(data))
                  s.(first_free_page).
Proof.

intros Hcr3 HPTlen Hdata HUnZero HIndex HRFree .
unfold all_cr3 in *.
rewrite in_map_iff in Hcr3.
unfold get_cr3 in *.
destruct Hcr3 as ( p & H & H2).
unfold page_table_length in *. unfold page_table_length_aux in *.
generalize ( HPTlen p ).
intro HPTlength.
destruct (le_dec nb_page s.(first_free_page)). 
(*inversion HFnZero.*)
 + constructor. assumption.
 + induction HRFree as [ffp HRfree | ffp HRfree H6 really_free]. 
      - contradict n. intuition.  
      - constructor 2.
        * assumption.
        * set (cr3_sublist := (firstn index (sublist (cr3 * page_size) nb_pte s.(data)) ++
               [0] ++ skipn (index + 1) (sublist (cr3 * page_size) nb_pte s.(data)))) in *. 
          clear IHreally_free really_free.
          unfold all_used_pages in *. rewrite in_flat_map in *.
          unfold not in *. intros H7. apply H6. destruct H7 as (p1 & H7 & H8).
          clear H6.
          unfold cr3_sublist in *.  clear cr3_sublist. subst.
          destruct (process_eq_dec p p1).
           { subst. replace (p.(cr3_save)) with p1.(cr3_save) in *. clear e. 
             exists p1. split. assumption.
               apply insert_zero_prop with s ffp p1 index in H8;intuition.
            }
           { exists p1. 
             split. assumption.
             apply in_sublist with (firstn (p.(cr3_save) * page_size) s.(data) ++
             (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
             [0] ++
             skipn (index + 1)
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) ++
             skipn (p.(cr3_save) * page_size + nb_pte) s.(data)).
             set (p_sublist := (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
             [0] ++
             skipn (index + 1)
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p1.(cr3_save) * page_size) (p.(cr3_save) * page_size)  nb_pte s.(data).
               - reflexivity. 
               - unfold p_sublist.
                 rewrite app_length.
                 rewrite app_length.
                 rewrite skipn_length.
                 rewrite firstn_length.
                 rewrite sublist_length.
                 Focus 2. 
                 unfold memory_length in Hdata.
                 rewrite <- Hdata.
                 replace nb_pte with page_size in *. 
                 replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
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
                 rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
                 replace (length [0]) with 1;auto with *.
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
                 apply n0.
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
            * destruct (le_dec nb_page (List.nth (ffp * page_size) s.(data) nb_page)).
              constructor. 
              rewrite <- insert_pte_nth with s cr3 index 0 ffp;intuition.
               {apply not_eq_and_le_lt ;trivial.
                 subst. unfold not. intros. apply H6. unfold all_used_pages. 
                 rewrite in_flat_map. exists p.
                 split;intuition. 
                 unfold process_used_pages. 
                 simpl. left. intuition. 
                 unfold page_size. simpl. omega. } 
               { rewrite insert_pte_nth   with s cr3 index 0 ffp in IHreally_free.
                 apply IHreally_free;trivial.
                 + clear IHreally_free.
                 rewrite <- insert_pte_nth;intuition.
                 apply not_eq_and_le_lt;trivial.
                   subst. unfold not. intros. apply H6.
                   unfold all_used_pages. 
                   rewrite in_flat_map. exists p.
                   split;intuition. 
                   unfold process_used_pages. 
                   simpl. left. intuition.
                   unfold page_size. simpl. omega.  
                 + apply not_eq_and_le_lt;trivial.
                   subst. unfold not. intros. apply H6. unfold all_used_pages. 
                   rewrite in_flat_map. exists p.
                   split;intuition. 
                   unfold process_used_pages. 
                   simpl. left. intuition. 
                   unfold page_size. simpl. omega.
                 + clear IHreally_free. assumption.
                 +  subst. apply HPTlen. assumption.
                 +  clear IHreally_free.  assumption. }
 Qed. 

Lemma not_cyclic_insert_pteZero_prop s cr3 index:
In cr3 (all_cr3 s.(process_list)) ->
(forall p , In p s.(process_list) -> p.(cr3_save) < nb_page) -> 
memory_length s ->

index < nb_pte ->
really_free s -> 
not_cyclic_aux s.(data) s.(first_free_page) [] ->
not_cyclic_aux
  (firstn (cr3 * page_size) s.(data) ++
   update_sublist index 0 (sublist (cr3 * page_size) nb_pte s.(data)) ++
   skipn (cr3 * page_size + nb_pte) s.(data)) s.(first_free_page) [].
Proof.  
intros Hcr3 HPTlen Hdata (*HFnZero*) HIndex HRFree HNcyc.
simpl in *.
destruct (le_dec nb_page s.(first_free_page)). (* inversion HFnZero. *)
      { constructor.  assumption. } 
      { inversion HRFree .
         + contradict H. intuition.
         + induction HNcyc.
           - contradict H2. intuition.
           - constructor 2; trivial.
           destruct (le_dec nb_page  (List.nth (pos * page_size) s.(data) nb_page )).
 
           (*inversion H1.*)
             * constructor . 
               unfold update_sublist. rewrite <- insert_pte_nth;intuition.
                { apply not_eq_and_le_lt;trivial.
                   + subst. unfold not. unfold all_cr3 in *.
                     rewrite in_map_iff in Hcr3.
                     unfold get_cr3 in *.
                     destruct Hcr3 as ( p & Hp & HInp).
                     unfold page_table_length in *. unfold page_table_length_aux in *.
                     generalize ( HPTlen p ).
                     intro HPTlength.
                     subst. clear IHHNcyc. 
                     intros.
                     apply H0. 
                     unfold all_used_pages. 
                     rewrite in_flat_map. 
                     exists p. 
                     split. assumption.
                     unfold process_used_pages. 
                     simpl. 
                     left. assumption.  
              
                  + unfold page_size. simpl. omega. }
               { unfold all_cr3 in*. rewrite in_map_iff in Hcr3.
                 destruct Hcr3. unfold page_table_length in *. 
                 unfold page_table_length_aux in *.
                 unfold get_cr3 in *.
                 generalize  (HPTlen x).
                 intros. destruct H4.   subst. intuition. }  
           * unfold update_sublist. rewrite <-insert_pte_nth;intuition.
              { unfold update_sublist in *.
                apply H4. intuition.
                inversion H1. 
                contradict H5. intuition. 
                apply H6. 
                inversion H1. 
                contradict H5. intuition. 
                assumption. }
              { apply not_eq_and_le_lt;trivial.
                subst.
                unfold not. unfold all_cr3 in *.
                rewrite in_map_iff in Hcr3.
                unfold get_cr3 in *.
                destruct Hcr3 as ( p & Hp & HInp).
                unfold page_table_length in *. unfold page_table_length_aux in *.
                generalize ( HPTlen p ).
                intro HPTlength.
                subst.  
                intros.
                apply H0. 
                unfold all_used_pages. 
                rewrite in_flat_map. 
                exists p. 
                split. assumption.
                unfold process_used_pages. 
                simpl. 
                left. assumption. 
                unfold page_size. simpl. omega. } 
              { unfold all_cr3 in*. rewrite in_map_iff in Hcr3.
                destruct Hcr3. unfold page_table_length in *. unfold page_table_length_aux in *.
                unfold get_cr3 in *.
                generalize  (HPTlen x).
                intros. destruct H5.  subst. intuition. } } 
Qed.


Lemma exists_page_get_index_page_le : 
forall page l index , length l = nb_pte ->
page = List.nth  index l 0 ->
index < nb_pte -> 
l = firstn index l ++
[page] ++ skipn (index + 1) l. 
Proof.
intros. rewrite Nat.add_1_r.
assert ( l = (firstn index l ++ skipn index l)).
rewrite List.firstn_skipn.
reflexivity.
rewrite  H2 at 1.
rewrite skipn_hd with index l 0.
rewrite H0. simpl. reflexivity.  
intuition.
Qed.

Lemma exists_page_nth_removePermission  : 
forall page l index , length l = nb_pte ->
page = removePermission (List.nth  index l 0) ->
index < nb_pte -> 
l = firstn index l ++
[new_pte page (
    getOffset
      (List.nth index l 0)
      permission_size )] ++ skipn (index + 1) l. 
Proof.
intros. rewrite Nat.add_1_r.
assert ( l = (firstn index l ++ skipn index l)).
rewrite List.firstn_skipn.
reflexivity.
rewrite  H2 at 1.
rewrite skipn_hd with index l 0.
rewrite H0. 
set (b := (List.nth index l 0)) in *.  
rewrite <-  add_remove_permission.
Opaque skipn.
simpl.  
Transparent skipn. 
reflexivity.  
intuition.
Qed.

Lemma in_mapped_pte_get_index_page_le s: 
forall p page index,
page = removePermission (List.nth index  (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0) ->
index < nb_pte -> 
page <> 0 ->
 In p s.(process_list) -> 
memory_length s ->  (forall p , In p s.(process_list) -> p.(cr3_save) < nb_page) ->
In page  (get_mapped_pte p.(cr3_save) s.(data)).
Proof.
intros p page index HPage HIndex Hpage0 Hp HData HPTlen.

unfold get_mapped_pte.
assert (exists permission , permission = getOffset (List.nth index
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0) permission_size /\ permission < 4).
eexists. split. reflexivity.
set ( b:= (List.nth index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0)).

apply permission_bound;trivial.

destruct H as (permission & H). 

rewrite  exists_page_get_index_page_le with (new_pte page permission ) 
 (sublist (p.(cr3_save) * page_size) nb_pte s.(data))
index;trivial.

 +   rewrite <- filter_app.
        rewrite <- filter_app.
        rewrite  map_app.
        rewrite  map_app. rewrite in_app_iff.
         rewrite in_app_iff. right.
         left. 
         simpl.
         case_eq (isMapped_pte (new_pte page permission)).
          - intros. simpl. left.
            apply remove_add_permission. intuition.
         - intros. contradict H0.

            unfold isMapped_pte in *.
            rewrite  remove_add_permission. 
            
            case_eq ( beq_nat page 0 ).
            intros.           apply beq_nat_true in H0.
            
            contradict Hpage0.
            assumption.
            intuition.
            apply beq_nat_false in H0.
            contradict H1.
            case_eq page.
            intros.
            contradict H.
            assumption.
            intros.
            intuition. intuition. 
  +  apply sublist_length.  unfold  memory_length in *. rewrite <- HData.
           replace nb_pte with page_size in *. 
           replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
           rewrite mult_comm.
           apply Nat.mul_le_mono_pos_l.
           unfold page_size. simpl. omega.    
           generalize (HPTlen p).
           intros. apply lt_le_S. 
           apply H0. assumption.  
           rewrite <-Nat.mul_succ_l. reflexivity.
           unfold page_size , nb_pte.
           simpl. omega.
   +rewrite HPage.
    set (b := (List.nth index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0)) in *.
    destruct H. rewrite H. 
    symmetry. 
    apply add_remove_permission.
Qed. 


Lemma removePte_NoDup s : 
forall p index page,
memory_length s ->  (forall p , In p s.(process_list) -> p.(cr3_save) < nb_page)->
In p s.(process_list) -> NoDup (process_used_pages s.(data) p) -> 
page = removePermission (List.nth index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0) -> 
index < nb_pte -> page <> 0 ->
 ~ In page (process_used_pages (firstn (p.(cr3_save) * page_size) s.(data) ++ 
                                update_sublist index 0 (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++ 
                                skipn (p.(cr3_save) * page_size + nb_pte) s.(data)) p).
Proof. 
intros p index page HData HPTlen Hp Hdup HPage HIndex HPage0.
set (l1 := firstn (p.(cr3_save) * page_size) s.(data) ) in *. 
set (l2 := skipn (p.(cr3_save) * page_size + nb_pte) s.(data)) in *.
set (l3 := (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) in *.
assert (page = removePermission (List.nth index l3 0)) as HPage';trivial.
inversion Hdup.
unfold process_used_pages.
simpl.
apply and_not_or.
split. 
 +   
 apply in_mapped_pte_get_index_page_le   with s p page index in HPage;trivial.

   apply In_notIn with (get_mapped_pte p.(cr3_save) s.(data));intuition.
 + assert (index < nb_pte) as HI;trivial.
    apply in_mapped_pte_get_index_page_le   with s p page index in HPage;trivial.


   clear H H0 H1 x.
   unfold get_mapped_pte.
   rewrite sublist_eq_two_app.
    - rewrite sublist_zero_app_eq.
      * unfold update_sublist. 
        rewrite <- filter_app.
        rewrite <- filter_app.
        rewrite  map_app.
        rewrite  map_app.
        unfold get_mapped_pte in H2.
 
        assert (exists permission, (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) = 
        (firstn index
        (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++ [new_pte page permission ] ++
        skipn (index + 1)
        (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) /\ permission < 4). 
         { assert (index < nb_pte) as HI';trivial.
           exists ( getOffset (List.nth index
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0) permission_size).
           unfold l3 in *. clear l3.
           split. 
           set (l3 := (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) in *.  
     
           apply exists_page_get_index_page_le;trivial.
           unfold l3. 
           apply sublist_length.  unfold  memory_length in *. rewrite <- HData.
           replace nb_pte with page_size in *. 
           replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
           rewrite mult_comm.
           apply Nat.mul_le_mono_pos_l.
           unfold page_size. simpl. omega.    
           generalize (HPTlen p).
           intros. apply lt_le_S. 
           apply H. assumption.  
           rewrite <-Nat.mul_succ_l. reflexivity.
           unfold page_size , nb_pte.
           simpl. omega.
           unfold l3 in *.
           set (b := (List.nth index (sublist (p.(cr3_save) * page_size) 
           nb_pte s.(data)) 0)) in *.
           rewrite HPage'. rewrite add_remove_permission. reflexivity.
           apply permission_bound.
           } 
         
        {unfold l3 in *.
         clear l3. 
         set (l3 := (sublist (p.(cr3_save) * page_size) nb_pte s.(data))) in *.
         destruct H.
         destruct H as (H & Hperm). 
         rewrite H in H2. 
         rewrite <- filter_app in H2.
         rewrite <- filter_app in H2.
         rewrite  map_app in H2.
         rewrite  map_app in H2.
         simpl in H2. 
         case_eq (isMapped_pte (new_pte page x)) .
         { intros. 
            rewrite H0 in H2. simpl in H2.
           apply NoDup_remove_2 in H2.
           rewrite in_app_iff.
           rewrite in_app_iff.
           rewrite in_app_iff in H2.
           rewrite remove_add_permission in H2.
           apply not_or_and in H2.
           destruct H2. 
           apply and_not_or.
           split.
           assumption.
           apply and_not_or.
           split. 
           simpl. 
           intuition.
           assumption.
           assumption. }
         { intros.
            unfold isMapped_pte in H0.
            contradict H0.
            rewrite  remove_add_permission.
            case_eq page.
            intros.

            contradict H1. assumption.
            intros.
            intuition. assumption. }     }
       * unfold update_sublist. 
         symmetry.
         unfold l3.
         rewrite app_length.
         rewrite app_length.
         rewrite skipn_length.
         rewrite firstn_length.
         rewrite sublist_length.       
         rewrite min_l;trivial.
         rewrite Nat.sub_add_distr.
         rewrite Nat.add_sub_assoc.
         rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
         replace (length [0]) with 1;auto with *.
         intuition. intuition. intuition. 
         unfold memory_length in HData.
         rewrite <- HData.
         replace nb_pte with page_size in *. 
         replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
         rewrite mult_comm.
         apply Nat.mul_le_mono_pos_l.
         unfold page_size. simpl. omega.    
         generalize (HPTlen p).
         intros. apply lt_le_S. 
         apply H. assumption.  
         rewrite <-Nat.mul_succ_l. reflexivity.
         unfold page_size , nb_pte.
         simpl. omega.
        
    - unfold l1. 
      rewrite firstn_length.
      rewrite min_l;trivial.
      unfold memory_length in *. 
      rewrite <- HData.
      rewrite mult_comm.
      apply Nat.mul_le_mono_pos_l.
      unfold page_size. simpl. omega.    
      unfold page_table_length, page_table_length_aux in *.
      apply le_lt_or_eq_iff. left.
      apply HPTlen;trivial.
Qed.

Lemma used_page_not_free s p page : 
really_free s -> In p s.(process_list) -> 
In  page (get_mapped_pte p.(cr3_save) s.(data)) ->
Not_free s page.
Proof.
intros.
unfold Not_free, really_free in *.
induction H. 
 + constructor. 
   assumption.
 + constructor 2. 
   assumption.
   unfold all_used_pages in *.
   rewrite in_flat_map in H2.
   intuition.
   apply H2. 
   exists p. 
   split. assumption. 
   unfold process_used_pages.
   simpl. right.
   rewrite <- H4.
   assumption.
   assumption.
Qed.

Lemma pte_zero_not_free s p page index pos:
       memory_length s ->  In p s.(process_list) -> 
       index < nb_pte ->
       really_free_aux  s.(process_list) s.(data) pos ->
       Not_free_aux page s.(data) pos -> 
       ( forall p , In p s.(process_list) -> p.(cr3_save) < nb_page ) ->
       Not_free_aux page  (firstn (p.(cr3_save) * page_size) s.(data) ++
                           update_sublist index 0
                                         (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
                           skipn (p.(cr3_save) * page_size + nb_pte) s.(data)) pos.
Proof.
intros Hdata Hp HIndex HRFree HFnZero HPTlen .
simpl in *.
unfold really_free in *.
inversion HFnZero. 
 + constructor.  assumption.  
 + inversion HRFree.
    - contradict H2. intuition.
    - induction HFnZero.  
       * contradict H. intuition.
       * constructor 2; trivial. inversion H1.
          { constructor . 
            unfold update_sublist. 
            rewrite <- insert_pte_nth;intuition.
            apply not_eq_and_le_lt;trivial.
             + subst. unfold not. 
               unfold page_table_length in *.
               unfold page_table_length_aux in *.
               generalize ( HPTlen p ).
               intro HPTlength.
               subst. 
               intros.
               apply H3. 
               unfold all_used_pages. 
               rewrite in_flat_map. 
               exists p. 
               split. assumption.
               unfold process_used_pages. 
               simpl. 
               left. assumption.  
               
             + unfold page_size. simpl. omega. }
               
           { unfold update_sublist. rewrite <-insert_pte_nth;intuition.
              - unfold update_sublist in *.
                apply H10.
                inversion H4. 
                contradict H7. intuition. 
                apply H12. 
                inversion H4. 
                contradict H10. intuition. 
                assumption.
              - apply not_eq_and_le_lt;trivial.
                subst. unfold not. 
                unfold page_table_length in *.
                unfold page_table_length_aux in *.
                generalize ( HPTlen p ).
                intro HPTlength.
                subst. 
                intros.
                apply H3. 
                unfold all_used_pages. 
                rewrite in_flat_map. 
                exists p. 
                split. assumption.
                unfold process_used_pages. 
                simpl. 
                left. assumption.            
                unfold page_size. simpl. omega. }
Qed. 
 
Lemma update_sublist_eq s (p:process) x index val: 
(forall p1 : process , In p1 s.(process_list) -> p1.(cr3_save) < nb_page) ->
x.(cr3_save) <> p.(cr3_save) ->
memory_length s ->
In x s.(process_list) ->
In p s.(process_list) ->
index < nb_pte ->
sublist (p.(cr3_save) * page_size) nb_pte
  (firstn (x.(cr3_save) * page_size) s.(data) ++
   (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
    [val] ++
    skipn (index + 1) (sublist (x.(cr3_save) * page_size) nb_pte s.(data))) ++
   skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) =
sublist (p.(cr3_save) * page_size) nb_pte s.(data).
Proof.
intros HPTlen n HData Hx Hp HIndex.
 set (cr3_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
 [val] ++ skipn (index + 1) (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))). 
 rewrite sublist_unchanged with  
 cr3_sublist 
 (p.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
  + unfold cr3_sublist.  reflexivity. 
  + unfold cr3_sublist.
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
    rewrite mult_comm.
    apply Nat.mul_le_mono_pos_l.
    unfold page_size. simpl. omega.    
    generalize (HPTlen x).
    intros. apply lt_le_S. 
    apply H. assumption.  
    rewrite <-Nat.mul_succ_l. reflexivity.
    unfold page_size , nb_pte.
    simpl. omega.
    rewrite min_l;trivial.
    rewrite Nat.sub_add_distr.
    rewrite Nat.add_sub_assoc.
    rewrite Nat.add_sub_assoc with (length [val]) nb_pte index.
    replace (length [val]) with 1;auto with *.
    intuition. intuition. intuition. 
 +  unfold nb_pte. simpl.  omega. 
 + intuition.   
 + generalize (HPTlen p). intros. apply mult_lt_compat_r.
      * apply H. assumption.
      * unfold page_size.  simpl. omega.
 + generalize (HPTlen x). intros.  
      apply mult_le_compat_r. 
      subst. intuition.  
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
   apply and_gt_plus. split; omega. 
Qed.


Lemma insert_zero_prop2 s p pg index : 
In pg
       (get_mapped_pte p.(cr3_save)
          (firstn (p.(cr3_save) * page_size) s.(data) ++
           update_sublist index 0
             (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
           skipn (p.(cr3_save) * page_size + nb_pte) s.(data))) ->
In p s.(process_list) ->
memory_length s ->
p.(cr3_save) < nb_page ->
index < nb_pte -> 

In pg (get_mapped_pte p.(cr3_save) s.(data)).

Proof.
intros H HProcess HData HPTlen HIndex .
unfold get_mapped_pte in H.
simpl in H. 
rewrite in_map_iff in H.  
unfold process_used_pages. 
simpl. 
destruct H.
destruct H as (H1 & H2).  rewrite filter_In in H2.
   destruct H2 as (H2 & H).
  rewrite sublist_eq_two_app in H2.
  - rewrite sublist_app_le in H2.
     * unfold get_mapped_pte.
       rewrite in_map_iff.
       exists x.
       split. assumption. 
       rewrite filter_In.
       split.
        { rewrite sublist_ident in H2.   
           + rewrite <-  List.firstn_skipn with  nat index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)).
             subst. 
             apply in_app_or in H2. apply in_or_app.
             destruct H2.
              - left. assumption. 
              - simpl in H0. 
                destruct H0. 
                 * unfold isMapped_pte in H.
                   contradict H.
                   
                   case_eq (removePermission x );intros.
                   case_eq (getOffset x valid_bits).
                   intros.
                   intuition.
                   intros. 
                   rewrite <- H0 in H1.
                   unfold getOffset in H1. 
                  
                rewrite Nat.land_0_l in H1.
                contradict H1. intuition. 
                 
                rewrite <- H0 in H.
                unfold removePermission in H. 
                unfold getBase in *.
                unfold permission_size in *.
                simpl in H.
                contradict H.
                omega.
                 * right. 
                   apply In_skipn. assumption.
             
           + unfold update_sublist.
             rewrite app_length.
             rewrite app_length.
             rewrite skipn_length.
             rewrite firstn_length.
             rewrite sublist_length.
              { rewrite min_l;trivial.
                rewrite Nat.sub_add_distr.
                rewrite Nat.add_sub_assoc.
                replace (length [0]) with 1;auto with *.
                intuition. intuition. }
             { unfold memory_length in HData.
               rewrite <- HData.
               replace nb_pte with page_size in *. 
               replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
               rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
               unfold page_size. simpl. omega.
               apply lt_le_S. 
               destruct H.
               assumption.  
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega. } }
       {  assumption.  }
       
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
          replace (length [0]) with 1;auto with *.
          intuition. intuition. }
        { unfold memory_length in HData.
          rewrite <- HData.
          replace nb_pte with page_size in *. 
          replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
          rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
          unfold page_size. simpl. omega.
          apply lt_le_S.
          assumption.  
          rewrite <-Nat.mul_succ_l. reflexivity.
          unfold page_size , nb_pte.
          simpl. omega. }
  - rewrite firstn_length.
    apply min_l.
    unfold memory_length in *. 
    rewrite <- HData.
    intuition.
    rewrite mult_comm. apply mult_le_compat_l; trivial.  intuition.
    
Qed.

Lemma insert_pte_prop s pg1 val p1 index page : 
In pg1
       (process_used_pages
          (firstn (p1.(cr3_save) * page_size) s.(data) ++
           (firstn index
              (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++
            [val] ++
            skipn (index + 1)
              (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) ++
           skipn (p1.(cr3_save) * page_size + nb_pte) s.(data)) p1) ->
In p1 s.(process_list) ->
memory_length s ->
p1.(cr3_save) < nb_page->
index < nb_pte  ->  
 sublist (p1.(cr3_save) * page_size) nb_pte s.(data) =
firstn index (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++
[page] ++
skipn (index + 1) (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))->
(pg1 =   (removePermission val) \/    In pg1 (process_used_pages s.(data) p1)).
Proof.
intros H HProcess HData HPTlen HIndex HPage .
unfold index_free_pte_prop in *. 
unfold process_used_pages in H. 
unfold get_mapped_pte in H.
rewrite app_assoc with nat (firstn index
                   (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) ([val])
                   (skipn (index + 1)
                   (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) in H.
simpl in H. 
rewrite in_map_iff in H.  
unfold process_used_pages. 
simpl. 
destruct H.
 + right. left.  assumption.
 + destruct H. destruct H as (H & H2).  rewrite filter_In in H2.
   destruct H2 as (H2 & Htrue).
  rewrite sublist_eq_two_app in H2.
  - rewrite sublist_app_le in H2.
     * set (sublist_cr3 := ((firstn index
           (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++ 
           [val]) ++
           skipn (index + 1)
           (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
       rewrite sublist_ident in H2.
         { unfold sublist_cr3 in *.
 
           apply in_insert_app  with nat
           (firstn index (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))) 
           (skipn (index + 1) (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)))
           x val page in H2. 
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
              replace (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))
                  with (firstn index (sublist (p1.(cr3_save) * page_size) nb_pte s.(data)) ++
                      [page] ++  skipn (index + 1) (sublist (p1.(cr3_save) * page_size) nb_pte s.(data))).
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
              replace (length [val]) with 1;auto with *.
              intuition. intuition. 
           + unfold memory_length in HData.
             rewrite <- HData.
             replace nb_pte with page_size in *. 
             replace (p1.(cr3_save) * page_size + page_size) with (S p1.(cr3_save) * page_size).
             rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
             unfold page_size. simpl. omega.   
            
             intros. apply lt_le_S.
             assumption.  
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
          replace (length [val]) with 1;auto with *.
          intuition. intuition. }
        { unfold memory_length in HData.
          rewrite <- HData.
          replace nb_pte with page_size in *. 
          replace (p1.(cr3_save) * page_size + page_size) with (S p1.(cr3_save) * page_size).
          rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
          unfold page_size. simpl. omega.
          apply lt_le_S.
          assumption.  
          rewrite <-Nat.mul_succ_l. reflexivity.
          unfold page_size , nb_pte.
          simpl. omega. }
  - rewrite firstn_length.
    apply min_l.
    unfold memory_length in *. 
    rewrite <- HData.
    intuition.
    rewrite mult_comm. apply mult_le_compat_l; trivial.  intuition.
    
Qed. 
    
Lemma free_not_zero_prop s index pos x:
memory_length s ->

In x s.(process_list) ->
x.(cr3_save) < nb_page ->
really_free_aux s.(process_list) s.(data) pos -> 
In x.(cr3_save) (all_used_pages s.(data) s.(process_list)) -> 
index < nb_pte -> 
Free_notZero_aux s.(data) pos -> 
Free_notZero_aux
  (firstn (x.(cr3_save) * page_size) s.(data) ++
   update_sublist index 0 (sublist (x.(cr3_save) * page_size) page_size s.(data)) ++
   skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) pos.
Proof. 
intros HData Hx Hxcr3 HRFree HUcr3 HIndex HFNzero.
 inversion HRFree. 
  + constructor. 
    intuition. 
  +  induction HFNzero.
      * constructor. assumption.
      * constructor 2;trivial.
        unfold update_sublist in *.
        rewrite <- insert_pte_nth;trivial.
        { inversion H1. 
          constructor. trivial.
          apply IHHFNzero;trivial. 
           }
        { apply not_eq_and_le_lt;trivial.
          unfold not in *.
          intros.  apply H0. 
          rewrite <- H4. intuition. 
          unfold page_size. simpl.
          omega. }
Qed.
Lemma  update_pte_invariant_add0 index page :
{{ fun (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\ 
    index < nb_pte /\
    page = removePermission (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 )  /\
    page <> 0 /\ page < nb_page }} 
  update_pte  0 index 
 {{ fun _  (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\
    ~ In   page (all_used_pages s.(data) s.(process_list))/\ 
    Not_free s  page /\
    page  < nb_page /\ page <> 0 /\
    List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 =0 
      }}.
Proof.
eapply weaken.
 + eapply update_pte_wp.
 + intros. unfold consistent in *. simpl. 
   destruct H as (HIso &(HRFree & HNCyc & HData (*& HPTlen *)& Hdup & Hpage & Hcurp) & HIndex & HPage).
   simpl.  try repeat split. 
    - unfold isolation in *.
      intros p1 p2 pg1 H2 H3 H4 H5.
      (*simpl in HCr3.  unfold cr3_properties in *. 
      destruct HCr3 as (HCr3 & Hv1 & Hv2).
      unfold all_cr3 in HCr3.
      rewrite in_map_iff in HCr3.
      destruct HCr3. unfold get_cr3 in *.*)
      unfold update_sublist in *. 
      set (l1 := firstn (s.(cr3) * page_size) s.(data) ) in *. 
      set (l2 := skipn (s.(cr3) * page_size + nb_pte) s.(data)) in *.
      set (l3 := (sublist (s.(cr3) * page_size) nb_pte s.(data))) in *.
      unfold  currProcess_inProcessList in *.
      destruct Hcurp as (x &Hx & Hxs). 
      destruct (process_eq_dec3 x p1 p2) as [H7 | H7].
       * assumption. 
       * destruct H7 as [Hxp1 |Hxp2]. 
          { apply not_in_sublist with s.(data).
             + unfold l1, l2, l3 in *. rewrite <- Hxs in *.  

               apply update_sublist_eq;trivial.
               intuition. 
               (**********************)
               unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p0.(cr3_save)) p0).
               intros. 
               destruct H7;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.
               intuition.  
               (**********************)
             + unfold l1 ,l2, l3 in *. 
               subst. replace  (x.(cr3_save)) with p1.(cr3_save) in *.
               rewrite <- Hxs in *.  apply insert_zero_prop in H5;trivial.
               apply HIso with p1;trivial.
               intros.       
               unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p.(cr3_save)) p).
               intros. 
               destruct H0;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.
               }
          { unfold not. 
            intros. 
            contradict H5. 
            apply not_in_sublist with s.(data).
             + unfold l1, l2, l3 in *. rewrite <- Hxs in *.   
               apply update_sublist_eq;trivial.
               intuition. unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p0.(cr3_save)) p0).
               intros. 
               destruct H7;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.
               intuition.
             + unfold l1 ,l2, l3 in *. 
            subst. replace  (x.(cr3_save)) with p2.(cr3_save) in *.
            destruct HPage as (HPage & HV).            
            apply exists_page_nth_removePermission in  HPage. rewrite <- Hxs in *.  
            apply insert_pte_prop  with s pg1 0 p2 index (new_pte page
           (getOffset
              (List.nth index
                 (sublist (p2.(cr3_save) * page_size) nb_pte s.(data)) 0)
              permission_size))  in H;trivial.
            destruct H.
             { unfold process_used_pages.  simpl. apply and_not_or.
               split.
                + unfold page_notZero in *. 
                  unfold used_notZero in *.
                  unfold removePermission in H. 
                  unfold getBase in H. 
                  simpl in H.
                  contradict H. 
                  destruct Hpage as (Hpage & HF).
                  generalize (Hpage pg1 p1). 
                  intros.
                  apply H0;trivial.                  
                  unfold process_used_pages. simpl. left. assumption.
                +  unfold removePermission in H. 
                  unfold getBase in H. 
                  simpl in H.
                  unfold not in *. 
                  intros.
                  contradict H. 
                  unfold page_notZero in *. 
                  unfold used_notZero in *.
                  destruct Hpage as (Hpage & HF).
                  generalize (Hpage pg1 p1). 
                  intros.
                  apply H;trivial. 
                  unfold process_used_pages. 
                  simpl. 
                  right. assumption. }
             { generalize (HIso p2 p1 pg1).  
               intros. apply H0;trivial. intuition. }
             { unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p2.(cr3_save)) p2).
               intros. 
               destruct H0;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.  }
             { rewrite sublist_length. reflexivity. 
               unfold memory_length in HData.
               rewrite <- HData.
               replace nb_pte with page_size in *.
               rewrite <- Hxs in *. 
               replace (p2.(cr3_save) * page_size + page_size) with (S p2.(cr3_save) * page_size).
               rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
               unfold page_size. simpl. omega.
               apply lt_le_S. 
                unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p2.(cr3_save)) p2).
               intros. 
               destruct H0;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega. }   
               assumption. }
         * apply not_in_sublist with  s.(data) .
          { unfold l1, l2, l3 in *. destruct H7. 
            rewrite <- Hxs in *.  
            apply update_sublist_eq;trivial. intros. 
      unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p0.(cr3_save)) p0).
               intros. 
               destruct H6;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.
                } 
          { generalize (HIso p1 p2 pg1).  intros. apply H;trivial.    
          
            apply in_sublist with  (l1 ++ (firstn index l3 ++ [0] ++ skipn (index + 1) l3) ++ l2).
              + symmetry.  
                unfold l1, l2, l3 in *.  
               rewrite <- Hxs in *. 

                apply update_sublist_eq;trivial.
                intros. 
                unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (p0.(cr3_save)) p0).
               intros. 
               destruct H1;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial.
               intuition.
              + assumption. }  
    - unfold really_free in *. simpl.
      apply  really_free_insert_pteZero_prop;intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3. 
      apply in_map_iff.
      exists x.
      unfold get_cr3. 
      intuition. 
      unfold page_notZero in *.
      intuition.        
      unfold  page_notZero in *.
      unfold used_notZero in *.
      generalize (H3 (p.(cr3_save)) p).
      intros. 
      destruct H5;intuition. 
      unfold process_used_pages. 
      simpl. left. trivial.
      unfold page_notZero in *.
      intuition. 
    - unfold not_cyclic in *. simpl. 
      apply not_cyclic_insert_pteZero_prop;intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3. 
      apply in_map_iff.
      exists x.
      unfold get_cr3. 
      intuition.
      unfold  page_notZero in *.
      destruct Hpage as (HU &HF).
      unfold used_notZero in *.
      generalize (HU (p.(cr3_save)) p).
      intros. 
      destruct H3;intuition. 
      unfold process_used_pages. 
      simpl. left. trivial.
    - unfold memory_length. simpl.
      unfold update_sublist. rewrite app_length.
      rewrite app_length.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3. 
      rewrite <- Hxs in *.
      (*unfold page_table_length in *.
      unfold page_table_length_aux in *.
      generalize  (HPTlen x).
      intros. (*destruct H.  subst. intuition.*)*)
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
                unfold  page_notZero in *.
               destruct Hpage as (HU &HF).
               unfold used_notZero in *.
               generalize (HU (x.(cr3_save)) x).
               intros. 
               destruct H0;intuition. 
               unfold process_used_pages. 
               simpl. left. trivial. }
          { apply mult_succ_l. }
          { intuition. }
      * rewrite  <- HData.
        assert (x.(cr3_save) < nb_page). 
         unfold  page_notZero in *.
         destruct Hpage as (HU &HF).
         unfold used_notZero in *.
         generalize (HU (x.(cr3_save)) x).
         intros. 
         destruct H0;intuition. 
         unfold process_used_pages. 
         simpl. left. trivial.
        rewrite mult_comm. auto with *.
       *unfold  page_notZero in *.
         destruct Hpage as (HU &HF).
         unfold used_notZero in *.
         generalize (HU (x.(cr3_save)) x).
         intros. 
         destruct H0;intuition. 
         unfold process_used_pages. 
         simpl. left. trivial.
   - unfold noDuplic_processPages in *.
     unfold all_used_pages.
     simpl in *.
     intros. 
     unfold currProcess_inProcessList in *.
     destruct Hcurp as ( x & Hx & Hxs). 
     unfold all_cr3. 
     rewrite <- Hxs in *.
     unfold page_notZero in *.
     destruct (process_eq_dec x p).
     * replace (x.(cr3_save)) with (p.(cr3_save)) in *. 
       generalize (Hdup p ).
       intros.
       assert(In p s.(process_list));trivial.
       apply H0 in H. 
       inversion H.
       constructor. 
        { unfold not in *. 
          intros. 
          apply H4.
          apply  insert_zero_prop2  with index ;trivial.
          unfold  page_notZero in *.
          destruct Hpage as (HU &HF).
          unfold used_notZero in *.
          generalize (HU (p.(cr3_save)) p).
          intros. 
          destruct H7;intuition. 
          unfold process_used_pages. 
          simpl. left. trivial. }
        { assert (In p s.(process_list));trivial.
          apply H0 in H1. clear H4 H2 H3.
          unfold update_sublist.
             set(p_sublist := (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
              [0] ++
              skipn (index + 1) (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))).
          unfold get_mapped_pte.
             assert ((sublist (p.(cr3_save) * page_size) nb_pte
               (firstn (p.(cr3_save) * page_size) s.(data) ++
               p_sublist ++ skipn (p.(cr3_save) * page_size + nb_pte) s.(data)))
               = p_sublist ).
               - rewrite sublist_eq_two_app.
                  + rewrite sublist_zero_app_eq.
                     reflexivity.
                     symmetry.
                     apply insert_pte_length;trivial.
                     destruct Hpage as (HU& HF). 
                     unfold used_notZero in *. 
                     generalize (HU p.(cr3_save) p).
                     intros. 
                     destruct H2;trivial. 
                     unfold process_used_pages in *. 
                     simpl. 
                     intuition. 
                  + rewrite firstn_length.
                    rewrite Min.min_l.
                     reflexivity. 
                     unfold memory_length in *. rewrite  <- HData.
                     rewrite mult_comm.
                      assert (p.(cr3_save) < nb_page). 
                      unfold  page_notZero in *.
                      destruct Hpage as (HU &HF).
                      unfold used_notZero in *.
                      generalize (HU (p.(cr3_save)) p).
                      intros. 
                      destruct H2;intuition. 
                      unfold process_used_pages. 
                      simpl. left. trivial. auto with *.
              - rewrite H2.   
                   unfold p_sublist.         
                   rewrite <- filter_app.
                   rewrite <- filter_app.
                   simpl.
                   unfold get_mapped_pte in H5. 
                    *  assert (exists pg ,
                       (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) = 
                       (firstn index
                       (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++ [pg] ++
                       skipn (index + 1)
                       (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))).
                        { eexists. 
                          rewrite <- List.firstn_skipn at 1.
                          instantiate (2 := index). 
                          rewrite skipn_hd at 1.
                           + instantiate (2:=0).
                             instantiate (1:= List.nth index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0).
                             Opaque skipn.
                             simpl. 
                             rewrite Nat.add_1_r.
                             reflexivity. 
                             
                           + rewrite sublist_length.
                             assumption.
                             unfold memory_length in HData.
                             rewrite <- HData.
                             replace nb_pte with page_size in *.
                              - replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
                                 * rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                                   unfold page_size. simpl. omega.
                                   apply lt_le_S.     
                                   unfold  page_notZero in *.
                                   destruct Hpage as (HU &HF).
                                   unfold used_notZero in *.
                                   generalize (HU (p.(cr3_save)) p).
                                   intros. 
                                   destruct H3;intuition. 
                                   unfold process_used_pages. 
                                   simpl. left. trivial.  
                                 * rewrite <-Nat.mul_succ_l. reflexivity.
                              - unfold page_size , nb_pte.
                                simpl. omega. }
                        { destruct H3. 
                          rewrite H3 in H5. 
                          rewrite <- filter_app in H5.
                          rewrite <- filter_app in H5.
                          rewrite map_app in H5. 
                          rewrite map_app in H5. 
                          rewrite map_app.
                          simpl in H5. 
                          destruct (isMapped_pte x1).
                          simpl in H5. 
                          apply NoDup_remove_1 in H5.
                          assumption.
                          simpl in H5. 
                          assumption. } }

    * unfold noDuplic_processPages in *.
       intros.  Opaque update_sublist process_used_pages . simpl in *.
       Transparent update_sublist process_used_pages.
       unfold process_used_pages in *.
       generalize (Hdup p).
       intros.
       assert (
       get_mapped_pte p.(cr3_save) s.(data) =
       get_mapped_pte p.(cr3_save)
       (firstn (x.(cr3_save) * page_size) s.(data) ++
       update_sublist index 0
       (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
       skipn (x.(cr3_save) * page_size + nb_pte) s.(data))).
       unfold get_mapped_pte .
       f_equal. f_equal.
        { unfold update_sublist.
          set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
          [0] ++
          skipn (index + 1)
          (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
          rewrite sublist_unchanged with  
          p_sublist 
          (p.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
             
               { reflexivity. } 
               { unfold p_sublist.
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
                 unfold  page_notZero in *.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (x.(cr3_save)) x).
                 intros. 
                 destruct H1;intuition. 
                 unfold process_used_pages. 
                 simpl. left. trivial.  
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite min_l;trivial.
                 rewrite Nat.sub_add_distr.
                 rewrite Nat.add_sub_assoc.
                 rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
                 replace (length [0]) with 1;auto with *.
                 intuition. intuition. intuition. } 
               { unfold nb_pte. simpl.  omega. } 
               { intuition. } 
               { assert (p.(cr3_save) < nb_page). 
                 unfold  page_notZero in *.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (p.(cr3_save)) p).
                 intros. 
                 destruct H1;intuition. 
                 unfold process_used_pages. 
                 simpl. left. trivial.
                 apply Nat.mul_lt_mono_pos_r.
                 unfold page_size.  simpl. omega.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (p.(cr3_save)) p).
                 intros. 
                 destruct H1;intuition. }
               { assert(x.(cr3_save) < nb_page).  
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (x.(cr3_save)) x).
                 intros. 
                 destruct H1;intuition.
                  unfold process_used_pages. 
                 simpl. left. trivial.
                 apply mult_le_compat_r. intuition. }  
               { apply NNPP.   unfold not in *.
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
                 apply and_gt_plus. split; omega. } }
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
              update_sublist index 0
                (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
              skipn (s.(cr3) * page_size + nb_pte) s.(data);
      first_free_page := s.(first_free_page) |}.(process_list)) in *.
      simpl ((process_used_pages
          {|
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
                  update_sublist index 0
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                  skipn (s.(cr3) * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data) )) in *.
      unfold  page_notZero in *.
      unfold used_notZero in *.
      destruct Hpage as (H2 & HF).
      generalize (H2 pg1 p1).
      intros. 
      apply H1.
      intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3.
       rewrite <- Hxs in *.
      destruct (process_eq_dec p1 x).
      *
        replace (x.(cr3_save)) with (p1.(cr3_save)) in *.
        unfold process_used_pages in * .
        simpl in *.
        destruct H0. 
        left.
        intuition.
        right.
        apply insert_zero_prop2 with  index;trivial.
        unfold  page_notZero in *.

        generalize (H2 (p1.(cr3_save)) p1).
        intros. 
        destruct H3;intuition.
        
      * 
        apply in_sublist with (firstn (x.(cr3_save) * page_size) s.(data) ++
        update_sublist index 0 (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
        skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) .
        unfold update_sublist.
        set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
             [0] ++
             skipn (index + 1)
             (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p1.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
          { reflexivity. } 
          { unfold p_sublist.
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
            generalize (H2 (x.(cr3_save)) x).
            intros. 
            destruct H3;intuition. 
            unfold process_used_pages. 
            simpl. left. trivial.
            intuition.  
            rewrite <-Nat.mul_succ_l. reflexivity.
            unfold page_size , nb_pte.
            simpl. omega.
            rewrite min_l;trivial.
            rewrite Nat.sub_add_distr.
            rewrite Nat.add_sub_assoc.
            rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
            replace (length [0]) with 1;auto with *.
            intuition. intuition. intuition. } 
          { unfold nb_pte. simpl.  omega. } 
          { intuition. } 
          { apply mult_lt_compat_r.
                  * generalize (H2 (p1.(cr3_save)) p1).
                  intros. 
            destruct H3;intuition. 
            unfold process_used_pages. 
            simpl. left. trivial.
                  * unfold page_size.  simpl. omega. }
          { apply mult_le_compat_r.
            generalize (H2 (x.(cr3_save)) x).
            intros. 
            destruct H3;intuition. 
            unfold process_used_pages. 
            simpl. left. trivial. }  
          { apply NNPP.   unfold not in *.
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
            apply and_gt_plus. split; omega. }
          { assumption. }
            
      
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
              update_sublist index 0
                (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
              skipn (s.(cr3) * page_size + nb_pte) s.(data);
      first_free_page := s.(first_free_page) |}.(process_list)) in *.
      simpl ((process_used_pages
          {|
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
                  update_sublist index 0
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                  skipn (s.(cr3) * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data) )) in *.
      unfold  page_notZero in *.
      unfold used_notZero in *.
      destruct Hpage as (H2 & HF).
      generalize (H2 pg1 p1).
      intros. 
      apply H1.
      intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3.
       rewrite <- Hxs in *.
      destruct (process_eq_dec p1 x).
      *
        replace (x.(cr3_save)) with (p1.(cr3_save)) in *.
        unfold process_used_pages in * .
        simpl in *.
        destruct H0. 
        left.
        intuition.
        right.
        apply insert_zero_prop2 with  index;trivial.
        generalize (H2 (p1.(cr3_save)) p1).
        intros. 
        destruct H3;intuition. 
              
      * 
        apply in_sublist with (firstn (x.(cr3_save) * page_size) s.(data) ++
        update_sublist index 0 (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
        skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) .
        unfold update_sublist.
        set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
             [0] ++
             skipn (index + 1)
             (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p1.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
          { reflexivity. } 
          { unfold p_sublist.
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
            generalize (H2 (x.(cr3_save)) x).
            intros. 
            destruct H3;intuition. 
            unfold process_used_pages. 
            simpl. left. trivial.  
            rewrite <-Nat.mul_succ_l. reflexivity.
            unfold page_size , nb_pte.
            simpl. omega.
            rewrite min_l;trivial.
            rewrite Nat.sub_add_distr.
            rewrite Nat.add_sub_assoc.
            rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
            replace (length [0]) with 1;auto with *.
            intuition. intuition. intuition. } 
          { unfold nb_pte. simpl.  omega. } 
          { intuition. } 
          { apply mult_lt_compat_r.
                  * generalize (H2 (p1.(cr3_save)) p1).
                    intros. 
                    destruct H3;intuition. 
                    unfold process_used_pages. 
                    simpl. left. trivial.
                  * unfold page_size.  simpl. omega. }
          { apply mult_le_compat_r.
            generalize (H2 (x.(cr3_save)) x).
            intros. 
            destruct H3;intuition. 
            unfold process_used_pages. 
            simpl. left. trivial. }  
          { apply NNPP.   unfold not in *.
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
            apply and_gt_plus. split; omega. }
          { assumption. }
   - unfold page_notZero in *. unfold free_notZero. 
     Opaque update_sublist. simpl. Transparent update_sublist.
     unfold free_notZero in *.
     unfold cr3_properties in *.
     unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      rewrite <- Hxs in *.
     apply free_not_zero_prop;trivial.
     unfold used_notZero in *.
     destruct Hpage as (HU & HF). 
     generalize (HU x.(cr3_save) x).
     intros.
     destruct H;intuition. 
     unfold process_used_pages. 
     simpl.
     left. reflexivity.
     unfold all_used_pages. 
     apply in_flat_map. 
     exists x. 
     intuition. 
     unfold process_used_pages.
     simpl. intuition. 
     intuition. 
   - unfold currProcess_inProcessList in *. intuition.  
   - unfold noDuplic_processPages in *.
     unfold all_used_pages.
     rewrite in_flat_map.
     simpl.
     unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      rewrite <- Hxs in *.
      unfold all_cr3. 
     unfold not in *. 
     intros.
     destruct H as (p & Hp & HUPage). 
     destruct (process_eq_dec p x).
     * replace (x.(cr3_save)) with (p.(cr3_save)) in *.
       clear e.
       destruct HPage as (HP & HV).
       contradict HUPage.
       apply removePte_NoDup ;intuition.
       unfold  page_notZero in *.
       destruct Hpage as (HU &HF).
       unfold used_notZero in *.
       generalize (HU (p0.(cr3_save)) p0).
       intros. 
       destruct H2;intuition. 
       unfold process_used_pages. 
       simpl. left. trivial.
    *  destruct HPage as (HPage & Hpageprop).
       apply in_mapped_pte_get_index_page_le with s x page  index in HPage;trivial.
        { unfold isolation in *.
          set (l1 := firstn (x.(cr3_save) * page_size) s.(data) ) in *. 
          set (l2 := skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) in *.
          set (l3 := (sublist (x.(cr3_save) * page_size) nb_pte s.(data))) in *.
          contradict HUPage. 
          apply not_in_sublist with  s.(data).
            + unfold  update_sublist. 
              unfold l3 in *.
              set (cr3_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
              [0] ++ skipn (index + 1) (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))). 
              rewrite sublist_unchanged with  
              cr3_sublist 
              (p.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
                - unfold l1. unfold l2.  reflexivity. 
                - unfold index_free_pte_prop in HIndex.
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
                  unfold  page_notZero in *.
                  destruct Hpage as (HU &HF).
                  unfold used_notZero in *.
                  generalize (HU (x.(cr3_save)) x).
                  intros. 
                  destruct H;intuition. 
                  unfold process_used_pages. 
                  simpl. left. trivial.  
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  rewrite Nat.sub_add_distr.
                  rewrite Nat.add_sub_assoc.
                  rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
                  replace (length [0]) with 1;auto with *.
                  intuition. intuition. intuition. 
                - unfold nb_pte. simpl.  omega. 
                - intuition. 
                -  apply mult_lt_compat_r.
                  * unfold  page_notZero in *.
                    destruct Hpage as (HU &HF).
                    unfold used_notZero in *.
                    generalize (HU (p.(cr3_save)) p).
                    intros. 
                    destruct H;intuition. 
                    unfold process_used_pages. 
                    simpl. left. trivial. 
                   * unfold page_size.  simpl. omega.
                - apply mult_le_compat_r. 
                  unfold  page_notZero in *.
                  destruct Hpage as (HU &HF).
                  unfold used_notZero in *.
                  generalize (HU (x.(cr3_save)) x).
                  intros. 
                  destruct H;intuition. 
                  unfold process_used_pages. 
                  simpl. left. trivial.
                - apply NNPP.   unfold not in *.
                  intros H9.
                  apply n. unfold l1, l2 , l3 in *.
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
         + apply HIso with x; intuition. unfold process_used_pages. 
           simpl. right. assumption. }
           intuition.
           intros.
           unfold  page_notZero in *.
           destruct Hpage as (HU &HF).
           unfold used_notZero in *.
           generalize (HU (p0.(cr3_save)) p0).
           intros. 
           destruct H0;intuition. 
           unfold process_used_pages. 
           simpl. left. trivial.
           unfold process_used_pages. 
           simpl. left. trivial.
            
   - unfold Not_free in *. simpl. destruct HPage as (HPage & Hpageprop).
     unfold currProcess_inProcessList in *.
     destruct Hcurp as ( x & Hx & Hxs). 
     rewrite <- Hxs in *.
     apply in_mapped_pte_get_index_page_le with s x page  index in HPage;trivial.
     inversion HRFree.
      * constructor. assumption.  
      * apply used_page_not_free with s x page in HRFree;intuition. 
        apply pte_zero_not_free; intuition.
        unfold  page_notZero in *.
        destruct Hpage as (HU &HF).
        unfold used_notZero in *.
        generalize (HU (p.(cr3_save)) p).
        intros. 
        destruct H5;intuition. 
        unfold process_used_pages. 
        simpl. left. trivial.
      * intuition.
      * intros. unfold  page_notZero in *.
        destruct Hpage as (HU &HF).
        unfold used_notZero in *.
        generalize (HU (p.(cr3_save)) p).
        intros. 
        destruct H0;intuition. 
        unfold process_used_pages. 
        simpl. left. trivial.
   - intuition.
   - intuition.
   -  unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold update_sublist.
      set (l1 := (firstn index (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
      [0] ++ skipn (index + 1) (sublist (s.(cr3) * page_size) nb_pte s.(data))) ++
      skipn (s.(cr3) * page_size + nb_pte) s.(data)). 
      unfold sublist. rewrite firstn_nth.
      rewrite <- Hxs in *.
       * rewrite skipn_nth. rewrite app_nth2.
         { rewrite firstn_length.
           rewrite Min.min_l.
            + rewrite minus_plus.
              unfold l1 in *.
              rewrite app_nth1.
               - rewrite app_nth2.
                 Focus 2. rewrite firstn_length.   
                 rewrite sublist_length. 
                 rewrite Min.min_l. intuition. intuition.  
                 unfold memory_length in *. rewrite <- HData.
                 intuition.  
                 replace nb_pte with page_size.
                 subst.  intros.    intuition.        rewrite <- Hxs in *.
                 replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.
                 assert(x.(cr3_save) < nb_page).
                 unfold  page_notZero in *.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (x.(cr3_save)) x).
                 intros. 
                 destruct H;intuition. 
                 unfold process_used_pages. 
                 simpl. left. trivial.
                 intuition.  
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite firstn_length.
                 rewrite sublist_length. 
                 rewrite Min.min_l.
                 rewrite minus_diag.
                 rewrite app_nth1. simpl. trivial.
                 simpl. omega. intuition.       
                 replace nb_pte with page_size. 
                 unfold memory_length in *. rewrite <- HData.           
                       rewrite <- Hxs in *.  unfold page_table_length in *. 
                 unfold page_table_length_aux in *.
                 
                 replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.
                 assert(x.(cr3_save) < nb_page).
                 unfold  page_notZero in *.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (x.(cr3_save)) x).
                 intros. 
                 destruct H;intuition. 
                 unfold process_used_pages. 
                 simpl. left. trivial.
                 intuition.
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
               - rewrite app_length.
                 rewrite app_length.
                 rewrite firstn_length.
                 rewrite sublist_length.
                 rewrite Min.min_l.
                 intuition.
                 replace (length [0]) with 1;intuition. intuition.   
                 replace nb_pte with page_size. 
                 unfold memory_length in *. rewrite <- HData.
                 rewrite <- Hxs in *. unfold page_table_length in *. 
                 unfold page_table_length_aux in *.
                 unfold  page_notZero in *.
                 replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.
                 assert(x.(cr3_save) < nb_page).
                 unfold  page_notZero in *.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (x.(cr3_save)) x).
                 intros. 
                 destruct H;intuition. 
                 unfold process_used_pages. 
                 simpl. left. trivial.
                 intuition.
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
              + unfold memory_length in *. rewrite <- HData.
                rewrite mult_comm with page_size nb_page.
                apply mult_le_compat_r.  destruct Hpage as (HU& HF). 
                unfold used_notZero in *. 
                generalize (HU x.(cr3_save) x).
                intros. 
                destruct H;trivial. 
                unfold process_used_pages in *. 
                simpl. 
                intuition. intuition. }
  
            { rewrite firstn_length.
              rewrite Min.min_l.
              intuition.  
              unfold memory_length in *. 
              rewrite <- HData. rewrite mult_comm with page_size nb_page.
              apply mult_le_compat_r.
              unfold  page_notZero in *.
                 destruct Hpage as (HU &HF).
                 unfold used_notZero in *.
                 generalize (HU (x.(cr3_save)) x).
                 intros. 
                 destruct H;intuition. 
                 unfold process_used_pages. 
                 simpl. left. trivial. }
             
   * intuition.
Qed. 

(*
Definition index_properties s cr3 index_page page := 
 index_page < nb_pte (*/\
 index_page = fst (get_index_page beq_nat (sublist (cr3 *page_size) nb_pte s.(data)) page). *). (***** Lemma index page table ******)
*)
Definition page_properties s page :=
 ~ In page (all_used_pages s.(data) s.(process_list)) /\
 List.nth (page * page_size) s.(data) nb_page = s.(first_free_page) /\
 Not_free s page  /\
 page  < nb_page /\ page <>0. 

Lemma really_free_freepage page val s :
page_table_length s -> 
memory_length s ->
page < nb_page ->
Not_free s page ->
~ In page (all_used_pages s.(data) s.(process_list)) ->
  really_free_aux s.(process_list) s.(data)  s.(first_free_page)->
  really_free_aux s.(process_list) (firstn (page * page_size) s.(data) ++
          update_sublist 0 val
            (sublist (page * page_size) nb_pte s.(data)) ++
          skipn (page * page_size + nb_pte) s.(data)) s.(first_free_page).
Proof.
intros HPTlen Hdata Hpage HNFpage HNUPage HRfree .
inversion HNFpage as [H3 | H3  HPNFP HNfree]. 
 + constructor. assumption. 
 + induction HRfree as [pos Hpos | pos Hpos HNUpos really_free]. 
      - contradict Hpos. intuition.  
      - constructor 2.
        * assumption.
        * set (mem := (firstn (page * page_size) s.(data) ++
               update_sublist 0 pos (sublist (page * page_size) nb_pte s.(data)) ++
               skipn (page * page_size + nb_pte) s.(data))) in *.
          unfold all_used_pages in *. rewrite in_flat_map in *.
          unfold not in *. intros H7. apply HNUpos. destruct H7 as (p & H7 & H8).
          exists p. split. assumption.
          unfold mem in *. 
          apply in_sublist with ((firstn (page * page_size) s.(data) ++
          update_sublist 0 val
             (sublist (page * page_size) nb_pte s.(data)) ++
             skipn (page * page_size + nb_pte) s.(data)))  .
           { unfold  page_table_length in HPTlen.
             unfold memory_length in Hdata. unfold  page_table_length in HPTlen.  
             unfold page_table_length_aux in HPTlen.
             apply sublist_unchanged .
              +  unfold update_sublist.
                 rewrite app_length.
                 rewrite app_length.
                 rewrite skipn_length.
                 rewrite firstn_length.
                 rewrite sublist_length.
                 Focus 2. 
                 unfold memory_length in Hdata.
                 rewrite <- Hdata.
                 replace nb_pte with page_size in *. 
                 replace (page * page_size + page_size) with (S page * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.    
                 intuition.  
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite min_l;trivial.
                 unfold nb_pte.
                 omega.
              + unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega. 
              + rewrite <- Hdata . intuition.  
              + intuition. apply mult_lt_compat_r. apply HPTlen;intuition. unfold page_size. unfold offset_nb_bits.
                simpl. omega. 
              + apply mult_le_compat_r. intuition. 
              + (*destruct H7 as (Hxp1 & Hxp2).*)
                apply NNPP.   unfold not in *. intros H9.
                apply HNUPage.   
                 apply not_or_and in H9. simpl in H9.  
                destruct H9 as (H9 & H1).  
                apply not_le in H1. unfold page_size in H9. unfold page_size in H1.  unfold nb_pte in *.  
                unfold offset_nb_bits in H1. unfold offset_nb_bits in H9. simpl in H1 ,H9. 
                apply not_le in H9.
                exists p.
                split. assumption.
                unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. }
            { assumption. }
        
       * set (l1 := firstn (page * page_size) s.(data)) in *. 
         set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
         set (l3 := sublist (page * page_size) nb_pte s.(data)) in *.

inversion really_free. constructor. unfold update_sublist.   unfold l3, l2, l1 in *. rewrite <- insert_pte_nth;trivial. 
         apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega. unfold nb_pte. unfold base_virt_page__nb_bits. 
         simpl. omega.  unfold l3, l2, l1 in *.  
         unfold update_sublist in *. rewrite <- insert_pte_nth;trivial.
         apply IHreally_free;trivial .
inversion HNfree.
contradict H2. intuition.  assumption.  inversion HNfree. contradict H2.  intuition. assumption.
          apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.
 unfold nb_pte. unfold base_virt_page__nb_bits. 
         simpl. omega. 
Qed.

Lemma not_cyclic_update_free_pagelist s page val :
 page_table_length s -> 
memory_length s ->
page < nb_page ->
Not_free s page ->
~ In page (all_used_pages s.(data) s.(process_list)) ->
 not_cyclic_aux s.(data) s.(first_free_page) [] ->
not_cyclic_aux
  (firstn (page * page_size) s.(data) ++
   update_sublist 0 val
     (sublist (page * page_size) nb_pte s.(data)) ++
   skipn (page * page_size + nb_pte) s.(data)) s.(first_free_page) [].
Proof. 
 intros HPTlen Hdata Hpage HNFree HNUPage HNCyc.
 unfold  page_table_length in HPTlen.
 inversion HNFree.  constructor.  assumption. 
 induction HNCyc as [ pg seen Hpageval | pg seen Hpageval HNotSeen HNextCyc].
 contradict H. intuition. 
 constructor 2;trivial. inversion H1. 
 constructor . unfold update_sublist. rewrite <- insert_pte_nth;trivial. 
 apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.  
  * unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega.
  * unfold update_sublist in *. rewrite <- insert_pte_nth;trivial. apply IHHNextCyc;trivial.
    apply not_eq_sym in H0.  apply not_eq in H0.
    destruct H0.
     { left. apply Nat.mul_lt_mono_pos_r. unfold page_size. simpl. omega. assumption. } 
     { right.  auto with *.
       replace (page  * page_size + page_size) with (S page * page_size).
        + apply Nat.mul_le_mono_pos_r . unfold page_size. simpl. omega. apply gt_le_S. assumption.
        + apply mult_succ_l. }
     { unfold nb_pte. unfold base_virt_page__nb_bits. simpl. omega. }
Qed.


Lemma Not_free_update_freePageList_prop page val s:
       memory_length s ->  page < nb_page -> 
       Not_free s page ->
       Not_free_aux page  s.(data)  s.(first_free_page) ->
       Not_free_aux page
  (firstn (page * page_size) s.(data) ++
   update_sublist 0 val
     (sublist (page * page_size) nb_pte s.(data)) ++
   skipn (page * page_size + nb_pte) s.(data)) s.(first_free_page).
Proof.
intros Hdata Hpage H10  H0 .
inversion H10 as [H3 | H3  H4 H5]. 
 + constructor. assumption. 
 + induction H0 as [pos H | pos H H6 Not_free]. 
      - contradict H. intuition.  
      - constructor 2.
        * assumption.
        * assumption.
        * inversion H5. 
          constructor. unfold update_sublist in *. rewrite <- insert_pte_nth;trivial.
          apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega. unfold nb_pte.
          unfold base_virt_page__nb_bits. simpl.  omega. 
        unfold update_sublist in *.
         rewrite <- insert_pte_nth;trivial. apply IHNot_free;trivial .
          apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.
          unfold nb_pte.
          unfold base_virt_page__nb_bits. simpl.  omega. 
Qed.


Lemma free_not_zero_prop' s val index page pos :
memory_length s ->
(*In x s.(process_list) ->*)
really_free_aux s.(process_list) s.(data) pos -> 
 Not_free_aux page s.(data) pos ->
page < nb_page ->
page <>0 -> 
index < nb_pte -> 
Free_notZero_aux s.(data) pos -> 
Free_notZero_aux
  (firstn (page * page_size) s.(data) ++
   update_sublist index val (sublist (page * page_size) page_size s.(data)) ++
   skipn (page * page_size + nb_pte) s.(data)) pos.
Proof. 
intros HData (*Hx*) HRFree HPage HPageV1 HPageV2 HIndex HFNzero.
 inversion HRFree. 
  + constructor. 
    intuition. 
  + induction HFNzero.
      * constructor. assumption.
      * constructor 2;trivial.
        unfold update_sublist in *.
        rewrite <- insert_pte_nth;trivial.
        { inversion H1. 
          constructor. trivial.
          apply IHHFNzero;trivial. 
          inversion HPage.
          contradict H2. 
          intuition. assumption.
       }
        { apply not_eq_and_le_lt;trivial. 
unfold Not_free in *. 
inversion HPage. 
contradict H4. intuition. assumption. unfold page_size.  simpl.  omega.
}
Qed.

Lemma update_free_pages_list_invariant page index:
{{ fun (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\
    ~ In page (all_used_pages s.(data) s.(process_list)) /\ 
    Not_free s page  /\
    page  < nb_page /\ page <> 0 /\(List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) =0 }} 
update_free_pages_list page
{{ fun _ (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\

     page_properties s page/\ (List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 ) =0
}}.
Proof.
unfold update_free_pages_list.
eapply weaken.
 + apply modify_wp.
 + intros. Opaque update_sublist. 
   simpl.
   unfold consistent in *. 
   destruct H as (HIso & (HRFree & HNCyc & HData (*& HPTlen*) & HNDup) & HNUPage  & HNFree & HPage).
   try repeat split. 
    - unfold isolation in *. intros. 
      apply not_in_sublist with  s.(data) .
      * Transparent update_sublist. 
        unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn 0
        (sublist (page * page_size) nb_pte s.(data)) ++
        [s.(first_free_page)] ++
        skipn (0 + 1)
        (sublist (page * page_size)  nb_pte s.(data)))).
        rewrite sublist_unchanged with  
        page_sublist 
        (p2.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          { unfold l1. unfold l2.  reflexivity. }
          { unfold page_sublist.
            rewrite app_length.
            rewrite app_length.
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite sublist_length.
            Focus 2. 
            unfold memory_length in HData.
            rewrite <- HData.
            replace nb_pte with page_size in *. 
            replace (page * page_size + page_size) with (S page * page_size).
            rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
            unfold page_size. simpl. omega. intuition. 
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial. omega. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           { destruct HNDup as (HNDup & (HU & HF) & HCurr). apply mult_lt_compat_r.
                + unfold used_notZero in *.
                  generalize (HU (p2.(cr3_save)) p2).
                  intros. 
                  destruct H3;intuition. 
                  unfold process_used_pages. 
                  simpl. left. trivial.
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. intuition. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             apply HNUPage.  apply in_flat_map.  
              apply not_or_and in H9. simpl in H9. exists p2. split. assumption.  
             destruct H9 as (H9 & H10).  
             apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
             unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
             apply not_le in H9. 
             unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. } 
   
      * generalize (HIso p1 p2 pg1 ). intros H9. clear HIso. apply H9;trivial.
         clear H9. apply in_sublist with ((firstn (page * page_size) s.(data) ++
           update_sublist 0 s.(first_free_page)
             (sublist (page * page_size) nb_pte s.(data)) ++
           skipn (page * page_size + nb_pte) s.(data)))  .
          { (*unfold  page_table_length in HPTlen.
              *)
            unfold memory_length in HData.
            apply sublist_unchanged .
             + unfold update_sublist.
                 rewrite app_length.
                 rewrite app_length.
                 rewrite skipn_length.
                 rewrite firstn_length.
                 rewrite sublist_length.
                 Focus 2. 
                 unfold memory_length in HData.
                 rewrite <- HData.
                 replace nb_pte with page_size in *. 
                 replace (page * page_size + page_size) with (S page * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.    
                 intuition.  
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite min_l;trivial.
                 unfold nb_pte.
                 omega. 
             + unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega. 
             + rewrite <- HData . intuition.  
             + intuition. apply mult_lt_compat_r. 
               unfold page_notZero in *. 
               destruct H7 as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p1.(cr3_save) p1). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity. 
               unfold page_size. unfold offset_nb_bits.
               simpl. omega. 
             + apply mult_le_compat_r. intuition. 
             + (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             apply HNUPage.  apply in_flat_map.  
              apply not_or_and in H9. simpl in H9. exists p1. split. assumption.  
             destruct H9 as (H9 & H10).  
             apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
             unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
             apply not_le in H9. 
             unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. } 
           { assumption. }
     - unfold really_free in *. Opaque update_sublist. simpl in *. Transparent update_sublist. 
       apply really_free_freepage;trivial. intuition.
       unfold page_table_length.
       unfold page_table_length_aux.
       intros. 
       unfold page_notZero in *. 
       destruct H3 as (HU & HF).
       unfold used_notZero in *.
       generalize (HU  p.(cr3_save) p). 
       intros HUd.
       destruct HUd;intuition. 
       unfold process_used_pages.
       simpl. 
       left. 
       reflexivity.
       intuition.
       
     - unfold not_cyclic in *. Opaque update_sublist. simpl in *. Transparent update_sublist.  
       apply not_cyclic_update_free_pagelist; trivial.
       unfold page_table_length.
       unfold page_table_length_aux.
       intros. 
       unfold page_notZero in *. 
       destruct HNDup as (HNDup & H3 & Hcur). 
       destruct H3 as (HU & HF).
       unfold used_notZero in *.
       generalize (HU  p.(cr3_save) p). 
       intros HUd.
       destruct HUd;intuition. 
       unfold process_used_pages.
       simpl. 
       left. 
       reflexivity.
       intuition.
       
     - unfold memory_length in *. Opaque page_size.
       Opaque update_sublist. simpl in *. Transparent update_sublist.
    unfold update_sublist. rewrite app_length.
    rewrite app_length.
 
    rewrite insert_pte_length;intuition.
    rewrite firstn_length.     
    rewrite Min.min_l.
      * rewrite skipn_length.
        rewrite plus_assoc. 
        replace nb_pte with page_size. 
        rewrite <- le_plus_minus with (page * page_size + page_size) (length s.(data)).
        unfold memory_length in *. 
        rewrite HData. intuition. 
        unfold memory_length in *. 
        rewrite <- HData. intuition.   
        replace (page  * page_size + page_size) with ( S page * page_size);trivial. 
          { rewrite  mult_comm with page_size nb_page.
            apply Nat.mul_le_mono_pos_r .
              + simpl. Transparent page_size. unfold page_size. unfold page_size. simpl. omega.
              + apply gt_le_S. intuition. }
          { apply mult_succ_l. }
          { intuition. }
      * rewrite  <- HData.
        rewrite mult_comm. auto with *.
       * unfold nb_pte in *.  unfold base_virt_page__nb_bits.  simpl. omega.
  - unfold noDuplic_processPages in *.
    intros.  Opaque update_sublist process_used_pages . simpl in *.
    Transparent update_sublist process_used_pages. 
    destruct HNDup.
    unfold all_used_pages in HNUPage.
    rewrite in_flat_map in HNUPage.
    unfold process_used_pages in *.
    assert (
    get_mapped_pte p.(cr3_save) s.(data) = get_mapped_pte p.(cr3_save)
     (firstn (page * page_size) s.(data) ++
      update_sublist 0 s.(first_free_page)
        (sublist (page * page_size) nb_pte s.(data)) ++
      skipn (page * page_size + nb_pte) s.(data))).
      unfold get_mapped_pte.
      f_equal. f_equal.
      * Transparent update_sublist. 
        unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn 0
        (sublist (page * page_size) nb_pte s.(data)) ++
        [s.(first_free_page)] ++
        skipn (0 + 1)
        (sublist (page * page_size)  nb_pte s.(data)))).
        rewrite sublist_unchanged with  
        page_sublist 
        (p.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          { unfold l1. unfold l2.  reflexivity. }
          { unfold page_sublist.
            rewrite app_length.
            rewrite app_length.
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite sublist_length.
            Focus 2. 
            unfold memory_length in HData.
            rewrite <- HData.
            replace nb_pte with page_size in *. 
            replace (page * page_size + page_size) with (S page * page_size).
            rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
            unfold page_size. simpl. omega. intuition. 
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial. omega. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           { unfold page_notZero in *.
             destruct H1 as ((HU & HF) & HCurr).
             apply mult_lt_compat_r.
                + unfold used_notZero in *.
                  generalize (HU (p.(cr3_save)) p).
                  intros Hud. 
                  destruct Hud;intuition. 
                  unfold process_used_pages. 
                  simpl. left. trivial.
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. intuition. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             apply HNUPage.  apply not_or_and in H9. simpl in H9. exists p. split. assumption.  
             destruct H9 as (H9 & H10).  
             apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
             unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
             apply not_le in H9. 
             unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. } 
      * rewrite <- H2. apply H0;trivial.        

  -  simpl ( {|
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
          data := firstn (page * page_size) s.(data) ++
                  update_sublist 0 s.(first_free_page)
                    (sublist (page * page_size) nb_pte s.(data)) ++
                  skipn (page * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *. simpl in H.
        unfold page_notZero in *.
     destruct HNDup as (Hdup & (HU & HF) & Hcurp).  
     unfold used_notZero in *.
     generalize (HU pg1 p1).
     intro HUp.  apply HUp;trivial.
     unfold process_used_pages in *.
    assert (
    get_mapped_pte p1.(cr3_save) s.(data) = get_mapped_pte p1.(cr3_save)
     (firstn (page * page_size) s.(data) ++
      update_sublist 0 s.(first_free_page)
        (sublist (page * page_size) nb_pte s.(data)) ++
      skipn (page * page_size + nb_pte) s.(data))).
      unfold get_mapped_pte.
     f_equal. f_equal.
      * Transparent update_sublist.
 
 unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn 0
        (sublist (page * page_size) nb_pte s.(data)) ++
        [s.(first_free_page)] ++
        skipn (0 + 1)
        (sublist (page * page_size)  nb_pte s.(data)))).
        rewrite sublist_unchanged with  
        page_sublist 
        (p1.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          { unfold l1. unfold l2.  reflexivity. }
          { unfold page_sublist.
            rewrite app_length.
            rewrite app_length.
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite sublist_length.
            Focus 2. 
            unfold memory_length in HData.
            rewrite <- HData.
            replace nb_pte with page_size in *. 
            replace (page * page_size + page_size) with (S page * page_size).
            rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
            unfold page_size. simpl. omega. intuition. 
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial. omega. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           {  apply mult_lt_compat_r.
                + generalize (HU (p1.(cr3_save)) p1).
                  intros. 
                  destruct H1;intuition.
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. intuition. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             apply HNUPage.  apply not_or_and in H9. simpl in H9. unfold all_used_pages. 
             apply in_flat_map. exists p1. split. assumption.  
             destruct H9 as (H9 & H10).  
             apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
             unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
             apply not_le in H9. 
             unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. } 
      * rewrite H1. apply H0;trivial.
  -  simpl ( {|
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
          data := firstn (page * page_size) s.(data) ++
                  update_sublist 0 s.(first_free_page)
                    (sublist (page * page_size) nb_pte s.(data)) ++
                  skipn (page * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *. simpl in H.
        unfold page_notZero in *.
     destruct HNDup as (Hdup & (HU & HF) & Hcurp).  
     unfold used_notZero in *.
     generalize (HU pg1 p1).
     intro HUp.  apply HUp;trivial.
     unfold process_used_pages in *.
    assert (
    get_mapped_pte p1.(cr3_save) s.(data) = get_mapped_pte p1.(cr3_save)
     (firstn (page * page_size) s.(data) ++
      update_sublist 0 s.(first_free_page)
        (sublist (page * page_size) nb_pte s.(data)) ++
      skipn (page * page_size + nb_pte) s.(data))).
      unfold get_mapped_pte.
     f_equal. f_equal.
      * Transparent update_sublist.

 unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn 0
        (sublist (page * page_size) nb_pte s.(data)) ++
        [s.(first_free_page)] ++
        skipn (0 + 1)
        (sublist (page * page_size)  nb_pte s.(data)))).
        rewrite sublist_unchanged with  
        page_sublist 
        (p1.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          { unfold l1. unfold l2.  reflexivity. }
          { unfold page_sublist.
            rewrite app_length.
            rewrite app_length.
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite sublist_length.
            Focus 2. 
            unfold memory_length in HData.
            rewrite <- HData.
            replace nb_pte with page_size in *. 
            replace (page * page_size + page_size) with (S page * page_size).
            rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
            unfold page_size. simpl. omega. intuition. 
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial. omega. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           {  apply mult_lt_compat_r.
                + generalize (HU (p1.(cr3_save)) p1).
                  intros. 
                  destruct H1;intuition.
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. intuition. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             apply HNUPage.  apply not_or_and in H9. simpl in H9. unfold all_used_pages. 
             apply in_flat_map. exists p1. split. assumption.  
             destruct H9 as (H9 & H10).  
             apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
             unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
             apply not_le in H9. 
             unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. } 
      * rewrite H1. apply H0;trivial.

  - unfold page_notZero in *. unfold free_notZero. Opaque update_sublist.
    simpl. Transparent update_sublist.
    unfold free_notZero in *.    unfold currProcess_inProcessList in *.
    destruct HNDup as ( HNDup & (HU & HF) & Hcurp).
    destruct Hcurp as ( x & Hx & Hxs). 
    rewrite <- Hxs in *.
    apply free_not_zero_prop';trivial.
    intuition. intuition.  unfold nb_pte. simpl. omega.
  - unfold currProcess_inProcessList in *;intuition.
  - Opaque update_sublist. simpl in *. Transparent update_sublist.
     unfold all_used_pages in *.
     unfold all_used_pages in *. rewrite in_flat_map in *.
     unfold not in *. intros H7. apply HNUPage. destruct H7 as (p & H7 & H8).
     exists p. split. assumption.
     apply in_sublist with ((firstn (page * page_size) s.(data) ++
     update_sublist 0 s.(first_free_page)
     (sublist (page * page_size) nb_pte s.(data)) ++
     skipn (page * page_size + nb_pte) s.(data)))  .
     { 
       unfold memory_length in HData.
       apply sublist_unchanged .
        +  unfold update_sublist.
            rewrite app_length.
            rewrite app_length.
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite sublist_length.
            Focus 2. 
            unfold memory_length in HData.
            rewrite <- HData.
            replace nb_pte with page_size in *. 
            replace (page * page_size + page_size) with (S page * page_size).
            rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
            unfold page_size. simpl. omega. intuition. 
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial. omega.  
        + unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega. 
              + rewrite <- HData . intuition.  
              + intuition. apply mult_lt_compat_r. 
               unfold page_notZero in *. 
      
       destruct H3 as (HU & HF).
       unfold used_notZero in *.
       generalize (HU  p.(cr3_save) p). 
       intros HUd.
       destruct HUd;intuition. 
       unfold process_used_pages.
       simpl. 
       left. 
       reflexivity.
       intuition.
                 unfold page_size. unfold offset_nb_bits.
                simpl. omega. 
              + apply mult_le_compat_r. intuition. 
              + (*destruct H7 as (Hxp1 & Hxp2).*)
                apply NNPP.   unfold not in *. intros H9.
                apply HNUPage.   
                 apply not_or_and in H9. simpl in H9.  
                destruct H9 as (H9 & H1).  
                apply not_le in H1. unfold page_size in H9. unfold page_size in H1.  unfold nb_pte in *.  
                unfold offset_nb_bits in H1. unfold offset_nb_bits in H9. simpl in H1 ,H9. 
                apply not_le in H9.
                exists p.
                split. assumption.
                unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. }
            { assumption. }
 -  Opaque update_sublist. simpl in *.
    Transparent update_sublist.
    set (l:= update_sublist 0 s.(first_free_page)
     (sublist (page * page_size) nb_pte s.(data)) ++
        skipn (page * page_size + nb_pte) s.(data)). 
    rewrite app_nth2.
    * rewrite firstn_length. 
      rewrite Min.min_l.
      { intuition. 
        rewrite minus_diag. 
        unfold l. 
        unfold update_sublist. 
        simpl.
        reflexivity. 
  }
      { unfold memory_length in HData.
        rewrite <- HData. 
        rewrite mult_comm.
        apply Nat.mul_le_mono_pos_l.
        unfold page_size. simpl.
        omega. intuition. } 
    * rewrite firstn_length. 
      rewrite Min.min_l.
      { intuition. }
      { unfold memory_length in HData.
        rewrite <- HData. 
        rewrite mult_comm.
        apply Nat.mul_le_mono_pos_l.
        unfold page_size. simpl.
        omega. intuition. } 
 - unfold Not_free in *.  Opaque update_sublist. simpl in *. Transparent update_sublist. 

apply Not_free_update_freePageList_prop;trivial. intuition.
- intuition.
- intuition. 
- destruct HPage as (Hv1 & Hv2 & H0). 
  rewrite <- H0 at 3.
  f_equal.
  symmetry.
  
       apply sublist_unchanged .
        *  unfold update_sublist.
            rewrite app_length.
            rewrite app_length.
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite sublist_length.
            Focus 2. 
            unfold memory_length in HData.
            rewrite <- HData.
            replace nb_pte with page_size in *. 
            replace (page * page_size + page_size) with (S page * page_size).
            rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
            unfold page_size. simpl. omega. intuition. 
            rewrite <-Nat.mul_succ_l. reflexivity.
            unfold page_size , nb_pte.
            simpl. omega.
            rewrite min_l;trivial. omega.  
        * unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega. 
        * unfold memory_length in *. rewrite <- HData . intuition.  
        * intuition. apply mult_lt_compat_r.
          unfold currProcess_inProcessList in *.
          destruct H3 as ( x & Hx & Hxs). 
          rewrite <- Hxs in *. 
          destruct H2 as (HU& HF).
          unfold used_notZero in *. 
          generalize (HU x.(cr3_save) x).
          intros. 
          destruct H1;trivial. 
          unfold process_used_pages in *. 
          simpl. 
          intuition.
          unfold page_size.
          simpl. omega. 
        * apply mult_le_compat_r. intuition. 
        * assert (page <> s.(cr3)) as Hd.
          unfold not. 
          intro Hpcr3.
          contradict HNUPage.
          unfold all_used_pages. 
          apply in_flat_map.
          destruct HNDup as ( HNDup & (HU & HF) & Hcurp).
          destruct Hcurp as ( x & Hx & Hxs). 
          rewrite <- Hxs in *.
          exists x. intuition.
          unfold process_used_pages. 
          simpl. 
          left. symmetry. assumption.
          apply NNPP.   unfold not in *. intros H9.
          apply HNUPage.   
           apply not_or_and in H9. simpl in H9.  
          destruct H9 as (H9 & H1).  
          apply not_le in H1. unfold page_size in H9.
          unfold page_size in H1.  unfold nb_pte in *.  
          unfold offset_nb_bits in H1.
          unfold offset_nb_bits in H9. simpl in H1 ,H9. 
          apply not_le in H9.
          unfold all_used_pages.
          apply in_flat_map.
          destruct HNDup as ( HNDup & (HU & HF) & Hcurp).
          destruct Hcurp as ( x & Hx & Hxs). 
          rewrite <- Hxs in *.
          exists x. intuition.
          unfold process_used_pages. 
          simpl. 
          left. apply and_gt_plus. split; omega. 
Qed.
 
Lemma  free_page_update_memory_invariant index_page page :
{{ fun (s : state) => 
    isolation s.(data) s.(process_list) /\ consistent s /\ 
    index_page < nb_pte /\
    page = removePermission(List.nth index_page (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0)
/\
    page <> 0 /\  page < nb_page}} 
free_page_update_memory index_page page 
{{ fun _ (s : state) => 
    isolation s.(data) s.(process_list) /\ consistent s /\ 

    page_properties s page /\ (List.nth index_page
     (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0 


}}.
Proof.
unfold free_page_update_memory.  
eapply bind_wp_rev.  
eapply update_pte_invariant_add0.
intros [].
eapply update_free_pages_list_invariant.
Qed. 
(*
Lemma  free_page_update_memory_invariant' cr3 index_page page :
{{ fun (s : state) => 
    isolation s.(data) s.(process_list) /\ consistent s /\ 
    cr3_properties s cr3 /\
    index_page < nb_pte /\
    page = removePermission(List.nth index_page (sublist (cr3 * page_size) nb_pte s.(data)) 0)
/\
    page <> 0 /\  page < nb_page}} 
free_page_update_memory cr3 index_page page 
{{ fun _ (s : state) => 
    isolation s.(data) s.(process_list) /\ consistent s /\ 
    cr3_properties s cr3 /\
    page_properties s page /\ (List.nth index_page
     (sublist (cr3 * page_size) nb_pte s.(data)) 0) = 0 


}}.
Proof.
unfold free_page_update_memory.  
eapply bind_wp_rev.  

eapply update_pte_invariant_add0.

intros [].
eapply update_free_pages_list_invariant.
Qed. 
*)

Lemma not_cyc_add_free_page s ffp page seen : 
List.nth (page * page_size) s.(data) nb_page = ffp ->
page < nb_page -> 
~ In page seen ->
Not_free_aux page s.(data) ffp -> 
not_cyclic_aux s.(data) ffp seen -> 
not_cyclic_aux s.(data) page seen.
Proof.
intros.
subst.
constructor 2.
assumption.
assumption. 
inversion H2. 
+ constructor. assumption.
+ induction H3. contradict H. intuition.
  subst.
  inversion H5. 
  -subst.  constructor 2; try assumption.
    * simpl. apply and_not_or. intuition. 
    * constructor. assumption. 
  - constructor 2;try trivial.
    * simpl. apply and_not_or. intuition. 
    * apply  not_cyclic_aux_sublist with (page::pos::seen).
      apply IHnot_cyclic_aux;try assumption.
      simpl. apply and_not_or. intuition.  
      intuition.

Qed.
Lemma  update_first_free_page_invariant page index :
{{ fun s : state =>
   isolation s.(data) s.(process_list) /\
   consistent s /\
   page_properties s page /\  (List.nth index
     (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0  }} 
 update_first_free_page page 
{{ fun (_ : unit) (s : state) =>
   isolation s.(data) s.(process_list) /\
   consistent s  /\  (List.nth index
     (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0  }}.
Proof.
 eapply weaken.
 eapply update_first_free_page_wp. 
 intros.  unfold consistent in H.
 destruct H as (HIso & (HRFree & HNCyc
 & HData & HPTlen & HNDup) &  (HNUPage & HNext & HNFree & HPage) & HIndex).
   simpl.
   unfold consistent in *.
 
   unfold really_free , not_cyclic, memory_length, page_table_length in *.
   Opaque page_size.

   simpl in *.
   intuition.
   + constructor 2. 
     intuition. assumption.
     rewrite HNext;assumption.
   + unfold Not_free in *.
     apply not_cyc_add_free_page with s.(first_free_page);trivial.
     intuition.
   + unfold page_notZero, used_notZero , 
     free_notZero in *.
     simpl in *.
     intuition.
     constructor 2;trivial. rewrite HNext. assumption.
Qed.


Lemma  update_pte_invariant_add0' index:
{{ fun (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\
    index < nb_pte }} 
    update_pte_0  0 index 
 {{ fun page  (s : state) =>
    isolation s.(data) s.(process_list) /\ consistent s /\
match page with 
|inl p => ~ In   p (all_used_pages s.(data) s.(process_list))/\ 
          Not_free s  p /\
          p < nb_page /\ p <> 0 /\
          List.nth index (sublist (s.(cr3) *page_size) nb_pte s.(data)) 0 =0 
|_ => True
end
      }}.
Proof.
eapply weaken.
eapply update_pte_0_wp.
intros.  unfold consistent in *. simpl. 
destruct H as (HIso &(HRFree & HNCyc & HData (*& HPTlen*) & Hdup & HPage & Hcurp) &  HIndex (*& HPage*)).
simpl.
destruct( lt_dec (removePermission
  (List.nth index (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0))nb_page) as [Hpage1|Hpage1] .
destruct (lt_dec 0 (removePermission
     (List.nth index (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0))) as [Hpage2 | Hpage2].
left.
try repeat split.  apply lt_0_neq in Hpage2. intuition.  intuition. 
- unfold isolation in *.
intros p1 p2 pg1 H2 H3 H4 H5.
evar (page : nat).
unfold update_sublist in *. 
set (l1 := firstn (s.(cr3) * page_size) s.(data) ) in *. 
set (l2 := skipn (s.(cr3) * page_size + nb_pte) s.(data)) in *.
set (l3 := (sublist (s.(cr3) * page_size) nb_pte s.(data))) in *.
unfold  currProcess_inProcessList in *.
destruct Hcurp as (x &Hx & Hxs). 
destruct (process_eq_dec3 x p1 p2) as [H7 | H7].
       + assumption. 
       + destruct H7 as [Hxp1 |Hxp2]. 
          * apply not_in_sublist with s.(data).
             { unfold l1, l2, l3 in *. rewrite <- Hxs in *.  
               apply update_sublist_eq;trivial.
               intros.
               unfold page_notZero in *.
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p0.(cr3_save) p0). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               intuition.
               contradict H.
               rewrite Hxp1.
               assumption. }
             { unfold l1 ,l2, l3 in *. 
               subst. replace  (x.(cr3_save)) with p1.(cr3_save) in *.
               rewrite <- Hxs in *.  apply insert_zero_prop in H5;trivial.
               apply HIso with p1;trivial.
               intros. 
               unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p.(cr3_save) p). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               }
          * unfold not. 
            intros. 
            contradict H5. 
            apply not_in_sublist with s.(data).
             { unfold l1, l2, l3 in *. rewrite <- Hxs in *.   
               apply update_sublist_eq;trivial.
               intros.
               unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p0.(cr3_save) p0). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               
               rewrite Hxp2. 
               intuition. }
             { unfold l1 ,l2, l3 in *. 
               subst. replace  (x.(cr3_save)) with p2.(cr3_save) in *.
               destruct HPage as (HPage & HV).            
               assert (page = removePermission
               (List.nth index
              (sublist (p2.(cr3_save) * page_size) nb_pte s.(data)) 0)) as Hpage.
              unfold page. 
              reflexivity.              
              apply exists_page_nth_removePermission in  Hpage.
              rewrite <- Hxs in *.  
              apply insert_pte_prop  with s pg1 0 p2 index (new_pte page
              (getOffset
              (List.nth index
              (sublist (p2.(cr3_save) * page_size) nb_pte s.(data)) 0)
              permission_size))  in H;trivial.
              destruct H.
              + unfold process_used_pages.  simpl. apply and_not_or.
                split.
                 - unfold page_notZero in *. 
                  unfold used_notZero in *.
                  unfold removePermission in H. 
                  unfold getBase in H. 
                  simpl in H.
                  contradict H. 
                  (* destruct Hpage as (Hpage & HF). *)
                  generalize (HPage pg1 p1). 
                  intros.
                  apply H0;trivial.                  
                  unfold process_used_pages. simpl. left. assumption.
                -  unfold removePermission in H. 
                  unfold getBase in H. 
                  simpl in H.
                  unfold not in *. 
                  intros.
                  contradict H. 
                  unfold page_notZero in *. 
                  unfold used_notZero in *.
(*                   destruct Hpage as (Hpage & HF). *)
                  generalize (HPage pg1 p1). 
                  intros.
                  apply H;trivial. 
                  unfold process_used_pages. 
                  simpl. 
                  right. assumption. 
             + generalize (HIso p2 p1 pg1).  
               intros. apply H0;trivial. intuition.
             + unfold used_notZero in *.
               generalize (HPage  p2.(cr3_save) p2). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
                
             + rewrite sublist_length. reflexivity. 
               unfold memory_length in HData.
               rewrite <- HData.
               replace nb_pte with page_size in *.
               rewrite <- Hxs in *. 
               replace (p2.(cr3_save) * page_size + page_size) with (S p2.(cr3_save) * page_size).
               rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
               Transparent page_size. 
               unfold page_size. simpl.
               omega.
               
               apply lt_le_S.
               unfold used_notZero in *.
               generalize (HPage  p2.(cr3_save) p2). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.  
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.    
             + assumption. }
         + apply not_in_sublist with  s.(data) .
          { unfold l1, l2, l3 in *. destruct H7. 
            rewrite <- Hxs in *.  
            apply update_sublist_eq;trivial.
            intros.
             unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p0.(cr3_save) p0). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               } 
          { generalize (HIso p1 p2 pg1).  intros. apply H;trivial.    
          
            apply in_sublist with  (l1 ++ (firstn index l3 ++ [0] ++ skipn (index + 1) l3) ++ l2).
              + symmetry.  
                unfold l1, l2, l3 in *.  
               rewrite <- Hxs in *. 

                apply update_sublist_eq;trivial.
                intuition.
                 unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p0.(cr3_save) p0). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity. intuition.          
              + assumption. }  
  -  unfold really_free in *. simpl.
      apply  really_free_insert_pteZero_prop;intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3. 
      apply in_map_iff.
      exists x.
      unfold get_cr3. 
      intuition. 
      unfold page_notZero in *.
      intuition.
       unfold page_notZero in *.
               unfold used_notZero in *.
               generalize (H0  p.(cr3_save) p). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               unfold page_notZero in *.
               intuition. 
 -   unfold not_cyclic in *. simpl. 
      apply not_cyclic_insert_pteZero_prop;intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3. 
      apply in_map_iff.
      exists x.
      unfold get_cr3. 
      intuition.
       unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  p.(cr3_save) p). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               
 -    unfold memory_length. simpl.
      unfold update_sublist. rewrite app_length.
      rewrite app_length.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3. 
      rewrite <- Hxs in *.
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
                unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  x.(cr3_save) x). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               }
          { apply mult_succ_l. }
          { intuition. }
      * rewrite  <- HData.
        rewrite mult_comm.
        assert (x.(cr3_save) < nb_page). 
         unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  x.(cr3_save) x). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               auto with *.
               * unfold page_notZero in *. 
               destruct HPage as (HU & HF).
               unfold used_notZero in *.
               generalize (HU  x.(cr3_save) x). 
               intros HUd.
               destruct HUd;intuition. 
               unfold process_used_pages.
               simpl. 
               left. 
               reflexivity.
               
 -   unfold noDuplic_processPages in *.
     unfold all_used_pages.
     simpl in *.
     intros. 
     unfold currProcess_inProcessList in *.
     destruct Hcurp as ( x & Hx & Hxs). 
     unfold all_cr3. 
     rewrite <- Hxs in *.
     unfold page_notZero in *.
     destruct (process_eq_dec x p).
     * replace (x.(cr3_save)) with (p.(cr3_save)) in *. 
       generalize (Hdup p ).
       intros.
       assert(In p s.(process_list));trivial.
       apply H0 in H. 
       inversion H.
       constructor. 
        { unfold not in *. 
          intros. 
          apply H4.
          apply  insert_zero_prop2  with index ;trivial.
 
apply pagetable_position with s;intuition.
               }
        { assert (In p s.(process_list));trivial.
          apply H0 in H1. clear H4 H2 H3.
          unfold update_sublist.
             set(p_sublist := (firstn index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++
              [0] ++
              skipn (index + 1) (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))).
          unfold get_mapped_pte.
             assert ((sublist (p.(cr3_save) * page_size) nb_pte
               (firstn (p.(cr3_save) * page_size) s.(data) ++
               p_sublist ++ skipn (p.(cr3_save) * page_size + nb_pte) s.(data)))
               = p_sublist ).
               - rewrite sublist_eq_two_app.
                  + rewrite sublist_zero_app_eq.
                     reflexivity.
                     symmetry.
                     apply insert_pte_length;trivial.
                     destruct HPage as (HU& HF). 
                     unfold used_notZero in *. 
                     generalize (HU p.(cr3_save) p).
                     intros. 
                     destruct H2;trivial. 
                     unfold process_used_pages in *. 
                     simpl. 
                     intuition. 
                  + rewrite firstn_length.
                    rewrite Min.min_l.
                     reflexivity. 
                     unfold memory_length in *. rewrite  <- HData.
                     rewrite mult_comm.
                     assert (p.(cr3_save) < nb_page).                     

apply pagetable_position with s;intuition.
                     auto with * .
              - rewrite H2.   
                   unfold p_sublist.         
                   rewrite <- filter_app.
                   rewrite <- filter_app.
                   simpl.
                   unfold get_mapped_pte in H5. 
                    *  assert (exists pg ,
                       (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) = 
                       (firstn index
                       (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) ++ [pg] ++
                       skipn (index + 1)
                       (sublist (p.(cr3_save) * page_size) nb_pte s.(data)))).
                        { eexists. 
                          rewrite <- List.firstn_skipn at 1.
                          instantiate (2 := index). 
                          rewrite skipn_hd at 1.
                           + instantiate (2:=0).
                             instantiate (1:= List.nth index (sublist (p.(cr3_save) * page_size) nb_pte s.(data)) 0).
                             Opaque skipn.
                             simpl. 
                             rewrite Nat.add_1_r.
                             reflexivity. 
                             
                           + rewrite sublist_length.
                             assumption.
                             unfold memory_length in HData.
                             rewrite <- HData.
                             replace nb_pte with page_size in *.
                              - replace (p.(cr3_save) * page_size + page_size) with (S p.(cr3_save) * page_size).
                                 * rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                                   unfold page_size. simpl. omega.   
                                   apply lt_le_S. 
                                   apply pagetable_position with s;intuition.
            
                                 * rewrite <-Nat.mul_succ_l. reflexivity.
                              - unfold page_size , nb_pte.
                                simpl. omega. }
                        { destruct H3. 
                          rewrite H3 in H5. 
                          rewrite <- filter_app in H5.
                          rewrite <- filter_app in H5.
                          rewrite map_app in H5. 
                          rewrite map_app in H5. 
                          rewrite map_app.
                          simpl in H5. 
                          destruct (isMapped_pte x1).
                          simpl in H5. 
                          apply NoDup_remove_1 in H5.
                          assumption.
                          simpl in H5. 
                          assumption. } }

    * unfold noDuplic_processPages in *.
       intros.  Opaque update_sublist process_used_pages . simpl in *.
       Transparent update_sublist process_used_pages.
       unfold process_used_pages in *.
       generalize (Hdup p).
       intros.
       assert (
       get_mapped_pte p.(cr3_save) s.(data) =
       get_mapped_pte p.(cr3_save)
       (firstn (x.(cr3_save) * page_size) s.(data) ++
       update_sublist index 0
       (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
       skipn (x.(cr3_save) * page_size + nb_pte) s.(data))).
       unfold get_mapped_pte .
       f_equal. f_equal.
        { unfold update_sublist.
          set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
          [0] ++
          skipn (index + 1)
          (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
          rewrite sublist_unchanged with  
          p_sublist 
          (p.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
             
               { reflexivity. } 
               { unfold p_sublist.
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
                 assert ( x.(cr3_save) < nb_page).
                 apply pagetable_position with s;intuition.
                 apply lt_le_S. 
                 apply H1.   
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite min_l;trivial.
                 rewrite Nat.sub_add_distr.
                 rewrite Nat.add_sub_assoc.
                 rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
                 replace (length [0]) with 1;auto with *.
                 intuition. intuition. intuition. } 
               { unfold nb_pte. simpl.  omega. } 
               { intuition. } 
               { apply mult_lt_compat_r.
                  * apply pagetable_position with s;intuition. 
                  * unfold page_size.  simpl. omega. }
               { 
                 apply mult_le_compat_r.
                 assert (x.(cr3_save) < nb_page). 
                 apply pagetable_position with s;intuition. intuition. }  
               { apply NNPP.   unfold not in *.
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
                 apply and_gt_plus. split; omega. } }
               { rewrite H1 in H0. apply H0. assumption. }
  -   simpl ( {|
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
              update_sublist index 0
                (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
              skipn (s.(cr3) * page_size + nb_pte) s.(data);
      first_free_page := s.(first_free_page) |}.(process_list)) in *.
      simpl ((process_used_pages
          {|
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
                  update_sublist index 0
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                  skipn (s.(cr3) * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data) )) in *.
      unfold  page_notZero in *.
      unfold used_notZero in *.
      destruct HPage as (H2 & HF).
      generalize (H2 pg1 p1).
      intros. 
      apply H1.
      intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3.
       rewrite <- Hxs in *.
      destruct (process_eq_dec p1 x).
      *
        replace (x.(cr3_save)) with (p1.(cr3_save)) in *.
        unfold process_used_pages in * .
        simpl in *.
        destruct H0. 
        left.
        intuition.
        right.
        apply insert_zero_prop2 with  index;trivial.
        apply pagetable_position with s;intuition.
        
        
      * 
        apply in_sublist with (firstn (x.(cr3_save) * page_size) s.(data) ++
        update_sublist index 0 (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
        skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) .
        unfold update_sublist.
        set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
             [0] ++
             skipn (index + 1)
             (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p1.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
          { reflexivity. } 
          { unfold p_sublist.
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
            rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
            replace (length [0]) with 1;auto with *.
            intuition. intuition. intuition. } 
          { unfold nb_pte. simpl.  omega. } 
          { intuition. } 
          { apply mult_lt_compat_r.
                  * apply pagetable_position with s;intuition. 
                  * unfold page_size.  simpl. omega. }
          {  apply mult_le_compat_r.
          assert (x.(cr3_save) < nb_page). 
          apply pagetable_position with s;intuition. intuition. }  
          { apply NNPP.   unfold not in *.
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
            apply and_gt_plus. split; omega. }
          { assumption. }
           
      
 -    simpl ( {|
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
              update_sublist index 0
                (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
              skipn (s.(cr3) * page_size + nb_pte) s.(data);
      first_free_page := s.(first_free_page) |}.(process_list)) in *.
      simpl ((process_used_pages
          {|
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
                  update_sublist index 0
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
                  skipn (s.(cr3) * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data) )) in *.
      unfold  page_notZero in *.
      unfold used_notZero in *.
      destruct HPage as (H2 & HF).
      generalize (H2 pg1 p1).
      intros. 
      apply H1.
      intuition.
      unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold all_cr3.
       rewrite <- Hxs in *.
      destruct (process_eq_dec p1 x).
      *
        replace (x.(cr3_save)) with (p1.(cr3_save)) in *.
        unfold process_used_pages in * .
        simpl in *.
        destruct H0. 
        left.
        intuition.
        right.
        apply insert_zero_prop2 with  index;trivial.
        apply pagetable_position with s;intuition.
        
        
      * 
        apply in_sublist with (firstn (x.(cr3_save) * page_size) s.(data) ++
        update_sublist index 0 (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
        skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) .
        unfold update_sublist.
        set (p_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
             [0] ++
             skipn (index + 1)
             (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))) in *. 
             rewrite sublist_unchanged with  
             p_sublist 
             (p1.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
          { reflexivity. } 
          { unfold p_sublist.
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
            rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
            replace (length [0]) with 1;auto with *.
            intuition. intuition. intuition. } 
          { unfold nb_pte. simpl.  omega. } 
          { intuition. } 
          {  apply mult_lt_compat_r.
                  * apply pagetable_position with s;intuition.
                  * unfold page_size.  simpl. omega. }
          {  apply mult_le_compat_r.
             assert(x.(cr3_save)<nb_page).
             apply pagetable_position with s;intuition.
             intuition. }  
          { apply NNPP.   unfold not in *.
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
            apply and_gt_plus. split; omega. }
          { assumption. } 
 -   unfold page_notZero in *. unfold free_notZero. 
     Opaque update_sublist. simpl. Transparent update_sublist.
     unfold free_notZero in *.
     unfold cr3_properties in *.
     unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      rewrite <- Hxs in *.
     apply free_not_zero_prop;trivial.
     unfold used_notZero in *.
     destruct HPage as (HU & HF). 
     generalize (HU x.(cr3_save) x).
     intros.
     destruct H;intuition. 
     unfold process_used_pages. 
     simpl.
     left. reflexivity.
     unfold all_used_pages. 
     apply in_flat_map. 
     exists x. 
     intuition. 
     unfold process_used_pages.
     simpl. intuition.  
     intuition. 
  -  unfold currProcess_inProcessList in *. intuition. 
  - unfold noDuplic_processPages in *.
     unfold all_used_pages.
     rewrite in_flat_map.
     simpl.
     unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      rewrite <- Hxs in *.
      unfold all_cr3. 
     unfold not in *. 
     intros.
     destruct H as (p & Hp & HUPage). 
     destruct (process_eq_dec p x).
     * replace (x.(cr3_save)) with (p.(cr3_save)) in *.
       clear e.
       destruct HPage as (HP & HV).
       contradict HUPage.
       apply removePte_NoDup ;intuition.
       apply pagetable_position with s;intuition.
    *  evar (page :nat). 
    assert (page = removePermission
           (List.nth index
              (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) 0)) as Hpage.
              unfold page. 
              
              reflexivity.              

       apply in_mapped_pte_get_index_page_le with s x page  index in Hpage;trivial.
        { unfold isolation in *.
          set (l1 := firstn (x.(cr3_save) * page_size) s.(data) ) in *. 
          set (l2 := skipn (x.(cr3_save) * page_size + nb_pte) s.(data)) in *.
          set (l3 := (sublist (x.(cr3_save) * page_size) nb_pte s.(data))) in *.
          contradict HUPage. 
          apply not_in_sublist with  s.(data).
            +
              unfold  update_sublist. 
              unfold l3 in *.
              set (cr3_sublist := (firstn index (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) ++
              [0] ++ skipn (index + 1) (sublist (x.(cr3_save) * page_size) nb_pte s.(data)))). 
              rewrite sublist_unchanged with  
              cr3_sublist 
              (p.(cr3_save) * page_size) (x.(cr3_save) * page_size)  nb_pte s.(data).
                - unfold l1. unfold l2.  reflexivity. 
                - unfold index_free_pte_prop in HIndex.
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
                  unfold page_notZero in *. 
                  intuition. 
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  rewrite Nat.sub_add_distr.
                  rewrite Nat.add_sub_assoc.
                  rewrite Nat.add_sub_assoc with (length [0]) nb_pte index.
                  replace (length [0]) with 1;auto with *.
                  intuition. intuition. intuition. 
                - unfold nb_pte. simpl.  omega. 
                - intuition. 
                -  apply mult_lt_compat_r.
                   * apply pagetable_position with s;intuition.
                     unfold page_notZero in *. 
                     intuition. 
                   * unfold page_size.  simpl. omega.
                - 
                  apply mult_le_compat_r.
                  assert(x.(cr3_save) < nb_page).
                  apply pagetable_position with s;intuition.
   
                     unfold page_notZero in *. 
                     intuition.
                     intuition. 
                       
                - apply NNPP.   unfold not in *.
                  intros H9.
                  apply n. unfold l1, l2 , l3 in *.
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
         + apply HIso with x; intuition. unfold process_used_pages. 
           simpl. right. assumption. }
           intuition.
           intros. 
           apply pagetable_position with s;intuition.
                     unfold page_notZero in *. 
                     intuition. 
                     intuition.  unfold page_notZero in *. 
                     intuition.
 -   unfold Not_free in *. simpl. destruct HPage as (HPage & Hpageprop).
     unfold currProcess_inProcessList in *.
     destruct Hcurp as ( x & Hx & Hxs). 
     rewrite <- Hxs in *.
     evar (page : nat). 
      assert (page = removePermission
           (List.nth index
              (sublist (x.(cr3_save) * page_size) nb_pte s.(data)) 0)) as Hpage. unfold page. 
              
              reflexivity.              

     apply in_mapped_pte_get_index_page_le with s x page  index in Hpage;trivial.
     inversion HRFree.
      * constructor. assumption.  
      * apply used_page_not_free with s x page in HRFree;intuition. 
        apply pte_zero_not_free; intuition.
         apply pagetable_position with s;intuition.
      * intuition.
      * intros. 
       apply pagetable_position with s;intuition.
     
         
  - intuition. 
  - intuition. 
  -   unfold currProcess_inProcessList in *.
      destruct Hcurp as ( x & Hx & Hxs). 
      unfold update_sublist.
      set (l1 := (firstn index (sublist (s.(cr3) * page_size) nb_pte s.(data)) ++
      [0] ++ skipn (index + 1) (sublist (s.(cr3) * page_size) nb_pte s.(data))) ++
      skipn (s.(cr3) * page_size + nb_pte) s.(data)). 
      unfold sublist. rewrite firstn_nth.
      rewrite <- Hxs in *.
       * rewrite skipn_nth. rewrite app_nth2.
         { rewrite firstn_length.
           rewrite Min.min_l.
            + rewrite minus_plus.
              unfold l1 in *.
              rewrite app_nth1.
               - rewrite app_nth2.
                 Focus 2. rewrite firstn_length.   
                 rewrite sublist_length. 
                 rewrite Min.min_l. intuition. intuition.  
                 unfold memory_length in *. rewrite <- HData.
                 intuition.  
                 replace nb_pte with page_size.   intuition.
                 rewrite <- Hxs in *.
                 replace (x.(cr3_save) * page_size + page_size)
                 with (S x.(cr3_save) * page_size).
                 rewrite mult_comm.
                 apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.
                 intuition. 
                 assert(x.(cr3_save) < nb_page).
                  apply pagetable_position with s;intuition.
                  unfold page_notZero in *. 
                  intuition. auto with *. 
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
                 rewrite firstn_length.
                 rewrite sublist_length. 
                 rewrite Min.min_l.
                 rewrite minus_diag.
                 rewrite app_nth1. simpl. trivial.
                 simpl. omega. intuition.       
                 replace nb_pte with page_size. 
                 unfold memory_length in *. rewrite <- HData.           
                       rewrite <- Hxs in *.
                         
                 replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.
                 intuition.  
                  apply pagetable_position with s;intuition.
                  unfold  page_notZero in *. 
                  intuition.
                  
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
               - rewrite app_length.
                 rewrite app_length.
                 rewrite firstn_length.
                 rewrite sublist_length.
                 rewrite Min.min_l.
                 intuition.
                 replace (length [0]) with 1;intuition. intuition.   
                 replace nb_pte with page_size. 
                 unfold memory_length in *. rewrite <- HData.
                 rewrite <- Hxs in *.
                 replace (x.(cr3_save) * page_size + page_size) with (S x.(cr3_save) * page_size).
                 rewrite mult_comm. apply Nat.mul_le_mono_pos_l.
                 unfold page_size. simpl. omega.
                 intuition.  
                 assert (x.(cr3_save) < nb_page).
                 
                  apply pagetable_position with s;intuition.
                 unfold page_notZero in *. 
                 intuition.
auto with *. 
                 
                 rewrite <-Nat.mul_succ_l. reflexivity.
                 unfold page_size , nb_pte.
                 simpl. omega.
              + unfold memory_length in *. rewrite <- HData.
                rewrite mult_comm with page_size nb_page.
                apply mult_le_compat_r.  destruct HPage as (HU& HF). 
                unfold used_notZero in *. 
                generalize (HU x.(cr3_save) x).
                intros. 
                destruct H;trivial. 
                unfold process_used_pages in *. 
                simpl. 
                intuition. intuition. }
  
            { rewrite firstn_length.
              rewrite Min.min_l.
              intuition. 
              unfold page_table_length in *. 
              unfold page_table_length_aux in *.
  
              unfold memory_length in *. 
              rewrite <- HData. rewrite mult_comm with page_size nb_page.
              apply mult_le_compat_r. intuition.
              assert (x.(cr3_save) < nb_page).
               apply pagetable_position with s;intuition.
               unfold page_notZero in *.
               intuition. 
               auto with *. 
}
             
   * intuition.

-

 right.
   split.
   intuition.
   intuition. 
 - right.
  split. intuition. intuition. 
Qed.


Lemma  free_page_update_memory_invariant' index_page:
{{ fun (s : state) => 
    isolation s.(data) s.(process_list) /\ consistent s /\ 

    index_page < nb_pte }} 
free_page_update_memory' index_page
{{ fun page (s : state) => 
    isolation s.(data) s.(process_list) /\ consistent s /\ 

match page with 
|inl p =>
    page_properties s p /\ (List.nth index_page
     (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0
|_ => True
end 


}}.
Proof.
unfold free_page_update_memory.  
eapply bind_wp_rev.  
eapply update_pte_invariant_add0'.
intros .
destruct a.
eapply bind_wp_rev.
eapply update_free_pages_list_invariant.
intros.  eapply weaken.
eapply ret_wp.
intuition.
destruct u. 
eapply weaken.
eapply ret_wp.
intuition. 
Qed.  



Lemma  update_first_free_page_invariant2  page index :
{{ fun s : state =>
   isolation s.(data) s.(process_list) /\
   consistent s /\
   page_properties s page /\  (List.nth index
     (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0  }} 
 update_first_free_page page 
{{ fun (_ : unit) (s : state) =>
   isolation s.(data) s.(process_list) /\
   consistent s (* (List.nth index
     (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0 *)}}.
Proof.
 eapply weaken.
  eapply update_first_free_page_wp. 
  intros.  unfold consistent in H.
  destruct H as (HIso & (HRFree & HNCyc
 & HData & HPTlen & HNDup) & (HNUPage & HNext & HNFree & HPage) & HIndex).
   simpl.
   unfold consistent in *.
 
   unfold really_free , not_cyclic, memory_length, page_table_length in *.
   Opaque page_size.

   simpl in *.
   intuition.
   + constructor 2. 
     intuition. assumption.
     rewrite HNext;assumption.
   + unfold Not_free in *.

     apply not_cyc_add_free_page with s.(first_free_page);trivial.
     intuition.
   + unfold page_notZero, used_notZero , 
     free_notZero in *.
     simpl in *.
     intuition.
     
     constructor 2;trivial. rewrite HNext. assumption.
     
Qed.


Lemma remove_pte_invariant Vaddr: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  
      }}
 remove_pte  Vaddr
{{ fun _  (s :state) =>  isolation s.(data) s.(process_list)  /\ consistent s }}.

Proof.
unfold remove_pte.
intros.
case_eq (lt_dec (getBase Vaddr offset_nb_bits) nb_pte).
intros.
 + eapply bind_wp_rev.
   eapply weaken.  eapply free_page_update_memory_invariant'.
   intuition.
   intros [page|].
   eapply weaken.
   eapply update_first_free_page_invariant2.
   intros. intuition.
   instantiate (1:= (getBase Vaddr offset_nb_bits)).
   assumption. 
   destruct u. eapply weaken. eapply ret_wp. 
   intros.
   intuition.
 + intros.  eapply weaken. eapply ret_wp. 
   intros.
   intuition.
 
Qed.




Lemma remove_pte_invariant' Vaddr: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  
      }}
 remove_pte'  Vaddr
{{ fun res  (s :state) =>  isolation s.(data) s.(process_list)  /\ consistent s /\ 
       match res with 
       | true =>  (List.nth (getBase Vaddr offset_nb_bits)
                    (sublist (s.(cr3) * page_size) nb_pte s.(data)) 0) = 0
       | false => True 
       end }}.

Proof.

unfold remove_pte'.
intros.
case_eq (lt_dec (getBase Vaddr offset_nb_bits) nb_pte).
intros.
 + eapply bind_wp_rev.
   eapply weaken.  eapply free_page_update_memory_invariant'.
   intuition.
   intros [page|].
   eapply bind_wp_rev. 
   eapply update_first_free_page_invariant.
   intros []. 
   eapply weaken. 
   eapply ret_wp. 
   intuition.
    case_eq u.
    intros. subst.
   (* intros []. *)
    eapply weaken. eapply ret_wp. 
   intros.
   intuition.
 + intros.  eapply weaken. eapply ret_wp. 
   intros.
   intuition.  
Qed.