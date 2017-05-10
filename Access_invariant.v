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
Require Import Lib StateMonad HMonad MMU Alloc_invariants Properties LibOs 
Access PageTableManager MemoryManager MMU_invariant.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Lemma  read_phy_addr_invariant (phy_addr : nat): 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s   }}
 read_phy_addr phy_addr
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
eapply weaken.
eapply read_phy_addr_wp.
simpl.
intros.
case_eq (lt_dec phy_addr  (length (data s)) ).
+ left;intuition.
+ right;intuition.
Qed.

Lemma  read_invariant (Vaddr : nat): 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s   }}
 read Vaddr
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
unfold read. 
eapply bind_wp_rev.
 + eapply translate_invariant.
 + intros a.
   destruct a.
   - eapply weaken.
     eapply read_phy_addr_wp.
     simpl.
     intros.
     case_eq (lt_dec n  (length (data s)) ).
      * left;intuition.
      * right;intuition.
   - destruct e.
     * eapply weaken.
       eapply ret_wp.
       intuition.
       (*eapply bind_wp_rev.
       eapply weaken.
       eapply add_interruption_invariant.
       intros.
       intuition.
       intros [].
       eapply weaken.
       eapply ret_wp.
       intuition. *)
     * eapply weaken.
       eapply ret_wp.
       intuition.
Qed.

Lemma assign_invariant (v : nat) : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s   }}
 assign v
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
eapply weaken.
eapply assign_wp.
simpl.
intros.
unfold consistent in *;intuition.
Qed.


Lemma load_invariant (v : nat) : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s   }}
 load v
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
unfold load.
eapply bind_wp_rev.
+ eapply read_invariant.
+ destruct a. 
  - eapply assign_invariant.
  -   eapply assign_invariant. 
  (*simpl. eapply weaken. 
    eapply ret_wp.
    intuition.*) 
Qed.



Definition write_aux (val Paddr: nat) := 
let page := getBase Paddr offset_nb_bits in 
let index := getOffset Paddr offset_nb_bits in  
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
    data := firstn (page * page_size) s.(data) ++
             update_sublist index val
               (sublist (page * page_size) page_size s.(data)) ++
             skipn (page * page_size + nb_pte) s.(data)   
|}).
Lemma write_aux_wp (val Paddr: nat) (P : unit-> state-> Prop) :
let page := getBase Paddr offset_nb_bits in 
let index := getOffset Paddr offset_nb_bits in  
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
    data := firstn (page * page_size) s.(data) ++
             update_sublist index val
               (sublist (page * page_size) page_size s.(data)) ++
             skipn (page * page_size + nb_pte) s.(data) |}
}}
write_aux val Paddr {{ P }}.
Proof.
simpl.
apply modify_wp.
Qed.


Definition write (val Vaddr : nat) := 
perform Paddr := translate Vaddr in 
match Paddr with 
|inl paddr => write_aux val paddr
|inr _ => ret tt
end.

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
            {
  rewrite <- insert_pte_length with s cr3 index pte;intuition. }

       * unfold memory_length in *. rewrite <- HData. rewrite mult_comm with page_size nb_page.
         apply mult_le_compat_r. intuition.
    - unfold  l1. rewrite app_length.
      rewrite length_firstn_le.
       * replace (length cr3_sublist) with page_size.
         auto with *. rewrite <- insert_pte_length with s cr3 index pte;intuition.
       * unfold memory_length in *. rewrite <- HData. rewrite mult_comm with page_size nb_page.
         apply mult_le_compat_r. intuition. 
Qed.



Lemma really_free_freepage x page val index s :
isolation s.(data) s.(process_list) ->
In x s.(process_list) -> 
x.(cr3_save) = s.(cr3) ->
noDuplic_processPages s ->
page_table_length s -> 
memory_length s ->
page < nb_page ->
Not_free s page ->
index < page_size ->
In page (get_mapped_pte s.(cr3) s.(data)) ->
  really_free_aux s.(process_list) s.(data)  s.(first_free_page)->
  really_free_aux s.(process_list) 
(firstn (page * page_size) s.(data) ++
   update_sublist index val (sublist (page * page_size) page_size s.(data)) ++
   skipn (page * page_size + nb_pte) s.(data)) s.(first_free_page).
Proof.
intros HIso Hx Hxcr3 HNDup HPTlen Hdata Hpage HNFpage HIndex HNUPage HRfree .
inversion HNFpage as [H3 | H3  HPNFP HNfree]. 
 + constructor. assumption. 
 + induction HRfree as [pos Hpos | pos Hpos HNUpos really_free]. 
      - contradict Hpos. intuition.  
      - constructor 2.
        * assumption.
        * set (mem := (firstn (page * page_size) s.(data) ++
               update_sublist index val (sublist (page * page_size) page_size s.(data)) ++
               skipn (page * page_size + nb_pte) s.(data))) in *.
          unfold all_used_pages in *. rewrite in_flat_map in *.
          unfold not in *. intros H7. apply HNUpos. destruct H7 as (p & H7 & H8).
          exists p. split. assumption.
          unfold mem in *.
          destruct (process_eq_dec p x).
          {
          
          apply in_sublist with ((firstn (page * page_size) s.(data) ++
          update_sublist index val
             (sublist (page * page_size) page_size s.(data)) ++
             skipn (page * page_size + nb_pte) s.(data)))  .
             - unfold  page_table_length in HPTlen.
               unfold memory_length in Hdata.
               unfold  page_table_length in HPTlen.  
               unfold page_table_length_aux in HPTlen.
               apply sublist_unchanged .
               unfold update_sublist.
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
                 replace nb_pte with page_size. 
                 replace (length [val] ) with 1;trivial.
                 omega. intuition. intuition.
              + unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega. 
              + rewrite <- Hdata . intuition.  
              + intuition. apply mult_lt_compat_r. apply HPTlen;intuition. unfold page_size. unfold offset_nb_bits.
                simpl. omega. 
              + apply mult_le_compat_r. intuition. 
              + apply NNPP.   unfold not in *. intros H9.
                
              
              assert (p.(cr3_save) <> page).
              
                      unfold noDuplic_processPages in *. 
                      unfold page_notZero in *.
                      generalize (HNDup p).
                      intros.
                      apply H in H7. 
                      unfold process_used_pages in *. 
                      simpl in H7.
                      inversion H7. 
                      rewrite e in H2.
                      unfold not.
                      unfold not in H2. 
                      intros. apply H2. 
                      rewrite e in H5.
                      rewrite  H5 at 1.
                      rewrite Hxcr3 .
                      assumption.
              unfold not in *.
              apply H.
              apply not_or_and in H9.
              simpl in H9.  
              destruct H9 as (H9 & H10).  
              apply not_le in H10.
              unfold page_size in H9.
              unfold page_size in H10.  unfold nb_pte in *.  
              unfold offset_nb_bits in H10.
              unfold offset_nb_bits in H9. simpl in H10 ,H9. 
              apply not_le in H9. 
              unfold process_used_pages. simpl. 
              omega.
         - assumption. }
         { apply in_sublist with ((firstn (page * page_size) s.(data) ++
          update_sublist index val
             (sublist (page * page_size) page_size s.(data)) ++
             skipn (page * page_size + nb_pte) s.(data)))  .
             - unfold  page_table_length in HPTlen.
               unfold memory_length in Hdata.
               unfold  page_table_length in HPTlen.  
               unfold page_table_length_aux in HPTlen.
               apply sublist_unchanged .
               unfold update_sublist.
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
                 replace nb_pte with page_size. 
                 replace (length [val] ) with 1;trivial.
                 omega. intuition. intuition.
              + unfold nb_pte.  unfold base_virt_page__nb_bits. simpl. omega. 
              + rewrite <- Hdata . intuition.  
              + intuition. apply mult_lt_compat_r. apply HPTlen;intuition. unfold page_size. unfold offset_nb_bits.
                simpl. omega. 
              + apply mult_le_compat_r. intuition. 
              + apply NNPP.   unfold not in *. intros H9.
              
              assert (p.(cr3_save) <> page).
               * generalize (HIso x p page).
                 intros.
                 apply H in H7;trivial.
                  { unfold not in *. intros. 
                    apply H7. unfold process_used_pages.
                    simpl. left. assumption. }
                  { intuition. } 
                  { unfold process_used_pages.
                    simpl. 
                    right. intuition.  
                    rewrite Hxcr3. assumption. }
               * unfold not in *.
                apply H.
                apply not_or_and in H9.
                simpl in H9.  
                destruct H9 as (H9 & H10).  
                apply not_le in H10.
                unfold page_size in H9.
                unfold page_size in H10.  unfold nb_pte in *.  
                unfold offset_nb_bits in H10.
                unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                apply not_le in H9. 
                unfold process_used_pages. simpl. 
                omega.
            - assumption. }
        
       * set (l1 := firstn (page * page_size) s.(data)) in *. 
         set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
         set (l3 := sublist (page * page_size) page_size s.(data)) in *.
        
         inversion really_free. constructor. unfold update_sublist. 
         unfold l3, l2, l1 in *. 
         rewrite <- insert_pte_nth;trivial. 
         apply not_eq_and_le_lt;trivial. unfold page_size. simpl.
         omega. unfold nb_pte. unfold base_virt_page__nb_bits. 
         unfold l3, l2, l1 in *.  
         unfold update_sublist in *.
         rewrite <- insert_pte_nth;trivial.
         apply IHreally_free;trivial .
         inversion HNfree.
         contradict H2. intuition.
         assumption.  inversion HNfree. contradict H2.
         intuition. assumption.
         apply not_eq_and_le_lt;trivial.
         unfold page_size. simpl. omega.
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

Lemma free_not_zero_prop s val index page pos x:
memory_length s ->
In x s.(process_list) ->
really_free_aux s.(process_list) s.(data) pos -> 
In page (get_mapped_pte x.(cr3_save) s.(data)) ->
page < nb_page ->
index < nb_pte -> 
Free_notZero_aux s.(data) pos -> 
Free_notZero_aux
  (firstn (page * page_size) s.(data) ++
   update_sublist index val (sublist (page * page_size) page_size s.(data)) ++
   skipn (page * page_size + nb_pte) s.(data)) pos.
Proof. 
intros HData Hx HRFree HPage HPageV HIndex HFNzero.
 inversion HRFree. 
  + constructor. 
    intuition. 
  + assert(pos <> page). 
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
    - induction HFNzero.
      * constructor. assumption.
      * constructor 2;trivial.
        unfold update_sublist in *.
        rewrite <- insert_pte_nth;trivial.
        { inversion H1. 
          constructor. trivial.
          apply IHHFNzero;trivial. 
          inversion HFNzero.  contradict H8. intuition. 
          unfold not in *. intros. apply H6. 
          apply in_flat_map. 
          exists x.
          split;trivial.
          rewrite H11.
          unfold process_used_pages. 
          simpl. right.
          assumption. }
        { apply not_eq_and_le_lt;trivial. intuition. 
          unfold page_size. simpl.
          omega. }
Qed.


Lemma  write_aux_invariant val paddr:
{{ fun (s : state) => isolation s.(data) s.(process_list) /\ consistent s /\ 
                      exists page index , 
                     In page (get_mapped_pte s.(cr3) s.(data)) /\
                     
                      paddr = (page * page_size) + index /\
                      index < page_size
 

}} 
  write_aux val paddr 
{{ fun _  (s : state) => isolation s.(data) s.(process_list) /\ consistent s }}.
Proof.
eapply weaken.
eapply write_aux_wp.
intros. 
simpl .
unfold consistent in *.
destruct H as (HIso & (HRFree & HNCyc & HData (*& HPTlen*) & (HNDup & (HU & HF) & Hcurp ))  & ( page & index & HUse & Hpaddr & HIndex)).
rewrite Hpaddr.
destruct Hcurp as (x & Hx & Hxcr3).
rewrite <- Hxcr3 in HUse. 
assert (getBase (page * page_size + index) offset_nb_bits  = page) as HP. 
unfold getBase.
fold page_size. 
rewrite Nat.div_add_l.
rewrite Nat.div_small.
omega. assumption.
unfold page_size.
unfold  offset_nb_bits. simpl.  
intuition.
assert (getOffset (page * page_size + index) offset_nb_bits = index) as HI.
unfold getOffset. 
rewrite Nat.land_ones.
fold page_size.
rewrite plus_comm.
rewrite Nat.mod_add. 
rewrite Nat.mod_small_iff.
assumption.
intuition. intuition.
rewrite HP in *. rewrite HI in *. 
try repeat split.
 - unfold isolation in *. intros.
   apply not_in_sublist with  s.(data) .
     +  Transparent update_sublist. 
        unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        set (page_sublist := (firstn index
        (sublist (page * page_size) page_size s.(data)) ++
        [val] ++
        skipn (index + 1)
        (sublist (page * page_size)  page_size s.(data)))).
        destruct (process_eq_dec3 x p1 p2) as [H7 | H7].
        assumption.
        destruct H7 as [H7 | H7].
        { rewrite sublist_unchanged with  
          page_sublist 
          (p2.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          * unfold l1. unfold l2.  reflexivity. 
          * unfold page_sublist.
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
            (******************** S page <= nb_page *************************   OK   *) 
            
            unfold page_notZero in *.
            

            unfold used_notZero in *.
            apply gt_le_S.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H3.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial. 
            (**************** ------ ********************)
            
            rewrite <-Nat.mul_succ_l. reflexivity.
            unfold page_size , nb_pte.
            simpl. omega.
            rewrite min_l;trivial.
            replace (length [val]) with 1;trivial.
            replace page_size with nb_pte. 
            replace nb_pte with page_size. intuition.
            
            intuition.
            
            intuition.
            
            simpl. omega. 
          * unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. 
          * unfold memory_length in HData. intuition. 
          * apply mult_lt_compat_r.
                { apply pagetable_position with s;intuition. }
                { unfold page_size.  simpl. omega. } 
          * apply mult_le_compat_r. intuition.
            unfold page_notZero in *.
            

            unfold used_notZero in *.
            apply le_lt_or_eq_iff.
            left. 
            generalize (HU page x).
            intros. 
            apply H3.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
          * apply NNPP.   unfold not . intros H9.
            assert (p2.(cr3_save) <> page) as HNUPage.
            { 
              unfold noDuplic_processPages in *. 
              unfold page_notZero in *.            
              generalize (HIso x p2 page).
              intros.
              apply H3 in H;trivial.
               + unfold not in *. intros. 
                 apply H. unfold process_used_pages.
                 simpl. left. assumption.
               + rewrite H7. assumption.
               + unfold process_used_pages.
                 simpl. 
                 right. intuition. }
             { unfold not in *.
               apply HNUPage.
               apply not_or_and in H9.
               simpl in H9.  
               destruct H9 as (H9 & H10).  
               apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
               unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
               apply not_le in H9. 
               unfold process_used_pages. simpl. 
               omega. } }
       { rewrite sublist_unchanged with  
          page_sublist 
          (p2.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          * unfold l1. unfold l2.  reflexivity. 
          * unfold page_sublist.
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
            (******************** S page <= nb_page *************************   OK   *) 
            
            unfold page_notZero in *.
            

            unfold used_notZero in *.
            apply gt_le_S.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H3.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial. 
            (**************** ------ ********************)
            
            rewrite <-Nat.mul_succ_l. reflexivity.
            unfold page_size , nb_pte.
            simpl. omega.
            rewrite min_l;trivial.
            replace (length [val]) with 1;trivial.
            replace page_size with nb_pte. 
            replace nb_pte with page_size. intuition.
            
            intuition.
            
            intuition.
            
            simpl. omega. 
          * unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. 
          * unfold memory_length in HData. intuition. 
          * apply mult_lt_compat_r.
                { apply pagetable_position with s;intuition. }
                { unfold page_size.  simpl. omega. } 
          * apply mult_le_compat_r. intuition.
            unfold page_notZero in *.
            

            unfold used_notZero in *.
            apply le_lt_or_eq_iff.
            left. 
            generalize (HU page x).
            intros. 
            apply H3.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
          * apply NNPP.   unfold not . intros H9.
            assert (p2.(cr3_save) <> page) as HNUPage.
            { unfold noDuplic_processPages in *. 
              unfold page_notZero in *.
              generalize (HNDup p2).
              intros.
              apply H3 in H. 
              unfold process_used_pages in *. 
              simpl in H.
              inversion H. 
              rewrite <- H7 in H6.
              unfold not.
              unfold not in H6. 
              intros. apply H6. 
              rewrite <- H7 in H10.
              
              rewrite  H10 at 1.
              assumption. }
            
             { unfold not in *.
               apply HNUPage.
               apply not_or_and in H9.
               simpl in H9.  
               destruct H9 as (H9 & H10).  
               apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
               unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
               apply not_le in H9. 
               unfold process_used_pages. simpl. 
               omega. } }
          { rewrite sublist_unchanged with  
          page_sublist 
          (p2.(cr3_save) * page_size) (page * page_size)  nb_pte s.(data).
          * unfold l1. unfold l2.  reflexivity. 
          * unfold page_sublist.
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
            (******************** S page <= nb_page *************************   OK   *) 
            
            unfold page_notZero in *.
            

            unfold used_notZero in *.
            apply gt_le_S.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H3.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial. 
            (**************** ------ ********************)
            
            rewrite <-Nat.mul_succ_l. reflexivity.
            unfold page_size , nb_pte.
            simpl. omega.
            rewrite min_l;trivial.
            replace (length [val]) with 1;trivial.
            replace page_size with nb_pte. 
            replace nb_pte with page_size. intuition.
            
            intuition.
            
            intuition.
            
            simpl. omega. 
          * unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. 
          * unfold memory_length in HData. intuition. 
          * apply mult_lt_compat_r.
                { apply pagetable_position with s;intuition. }
                { unfold page_size.  simpl. omega. } 
          * apply mult_le_compat_r. intuition.
            unfold page_notZero in *.
            

            unfold used_notZero in *.
            apply le_lt_or_eq_iff.
            left. 
            generalize (HU page x).
            intros. 
            apply H5.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
          * apply NNPP.   unfold not . intros H9.
            assert (p2.(cr3_save) <> page) as HNUPage.
            { 
              unfold noDuplic_processPages in *. 
              unfold page_notZero in *.            
              generalize (HIso x p2 page).
              intros.
              apply H3 in H;trivial.
               + unfold not in *. intros. 
                 apply H. unfold process_used_pages.
                 simpl. left. assumption.
               + intuition. 
               + unfold process_used_pages.
                 simpl. 
                 right. intuition. }
             { unfold not in *.
               apply HNUPage.
               apply not_or_and in H9.
               simpl in H9.  
               destruct H9 as (H9 & H10).  
               apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
               unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
               apply not_le in H9. 
               unfold process_used_pages. simpl. 
               omega. } }
            
      + destruct (process_eq_dec3 x p1 p2) as [H7 | H7].
        { assumption. }
        { destruct H7 as [H7 | H7].
          - generalize (HIso p1 p2 pg1 ). intros H9.
            apply H9;trivial.
            clear H9.
            apply in_sublist with ((firstn (page * page_size) s.(data) ++
            update_sublist index val
            (sublist (page * page_size) page_size s.(data)) ++
            skipn (page * page_size + nb_pte) s.(data)))  .
             * unfold memory_length in HData. 
               apply sublist_unchanged .
                { unfold update_sublist.
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
                  unfold page_notZero in *.
                  
                  unfold used_notZero in *.
                  apply gt_le_S.
                  replace (nb_page > page) with (page< nb_page).
                  unfold page_notZero in *.
                  generalize (HU page x).
                  intros. 
                  apply H3.
                  assumption.
                  unfold process_used_pages.
                  simpl. right.
                  assumption.
                  trivial. 
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  replace (length [val]) with 1;trivial.
                  replace page_size with nb_pte. 
                  replace nb_pte with page_size in *. 
                  omega. intuition. intuition.           
                  intuition. }
                { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. }
                { unfold memory_length in HData. intuition. }
                { apply mult_lt_compat_r.
                   - apply pagetable_position with s;intuition. 
                   - unfold page_size.  simpl. omega. }
                { apply mult_le_compat_r.
                  apply le_lt_or_eq_iff.
                  left. 
                  
                  unfold used_notZero in *.         
                  unfold page_notZero in *.
                  generalize (HU page x).
                  intros. 
                  apply H3.
                  assumption.
                  unfold process_used_pages.
                  simpl. right.
                  assumption. }
                { apply NNPP.   unfold not. intros H9.
                  assert (p1.(cr3_save) <> page) as HNUPage.
                    + 
                      unfold noDuplic_processPages in *. 
                      unfold page_notZero in *.
                      generalize (HNDup p1).
                      intros.
                      apply H3 in H0. 
                      unfold process_used_pages in *. 
                      simpl in H0.
                      inversion H0. 
                      rewrite <- H7 in H6.
                      unfold not.
                      unfold not in H6. 
                      intros. apply H6. 
                      rewrite <- H7 in H10.
                      rewrite  H10 at 1.
                      assumption. 
                    + unfold not in *.
                      apply HNUPage.
                      apply not_or_and in H9.
                      simpl in H9.  
                      destruct H9 as (H9 & H10).  
                      apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
                      unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                      apply not_le in H9. 
                      unfold process_used_pages. simpl. 
                      omega. } 
              * assumption.
         - generalize (HIso p1 p2 pg1 ). intros H9.
            apply H9;trivial.
            clear H9.
            apply in_sublist with ((firstn (page * page_size) s.(data) ++
            update_sublist index val
            (sublist (page * page_size) page_size s.(data)) ++
            skipn (page * page_size + nb_pte) s.(data)))  .
             * unfold memory_length in HData.
               apply sublist_unchanged .
                { unfold update_sublist.
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
                  unfold page_notZero in *.
                  
                  unfold used_notZero in *.
                  apply gt_le_S.
                  replace (nb_page > page) with (page< nb_page).
                  unfold page_notZero in *.
                  generalize (HU page x).
                  intros. 
                  apply H3.
                  assumption.
                  unfold process_used_pages.
                  simpl. right.
                  assumption.
                  trivial. 
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  replace (length [val]) with 1;trivial.
                  replace page_size with nb_pte. 
                  replace nb_pte with page_size in *. 
                  omega. intuition. intuition.           
                  intuition. }
                { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. }
                { unfold memory_length in HData. intuition. }
                { apply mult_lt_compat_r.
                   - apply pagetable_position with s;intuition. 
                   - unfold page_size.  simpl. omega. }
                { apply mult_le_compat_r.
                  apply le_lt_or_eq_iff.
                  left. 
                  
                  unfold used_notZero in *.         
                  unfold page_notZero in *.
                  generalize (HU page x).
                  intros. 
                  apply H3.
                  assumption.
                  unfold process_used_pages.
                  simpl. right.
                  assumption. }
                { apply NNPP.   unfold not. intros H9.
                  assert (p1.(cr3_save) <> page) as HNUPage.
                    + generalize (HIso x p1 page).
                      intros.
                      apply H3 in H0;trivial.
                      - unfold not in *. intros. 
                        apply H0. unfold process_used_pages.
                        simpl. left. assumption.
                      - intuition. 
                      - unfold process_used_pages.
                        simpl. 
                        right. intuition.  
                    + unfold not in *.
                      apply HNUPage.
                      apply not_or_and in H9.
                      simpl in H9.  
                      destruct H9 as (H9 & H10).  
                      apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
                      unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                      apply not_le in H9. 
                      unfold process_used_pages. simpl. 
                      omega. } 
              * assumption. }
         { generalize (HIso p1 p2 pg1 ). intros H9.
            apply H9;trivial.
            clear H9.
            apply in_sublist with ((firstn (page * page_size) s.(data) ++
            update_sublist index val
            (sublist (page * page_size) page_size s.(data)) ++
            skipn (page * page_size + nb_pte) s.(data)))  .
             * unfold memory_length in HData. 
               apply sublist_unchanged .
                { unfold update_sublist.
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
                  unfold page_notZero in *.
                  
                  unfold used_notZero in *.
                  apply gt_le_S.
                  replace (nb_page > page) with (page< nb_page).
                  unfold page_notZero in *.
                  generalize (HU page x).
                  intros. 
                  apply H3.
                  assumption.
                  unfold process_used_pages.
                  simpl. right.
                  assumption.
                  trivial. 
                  rewrite <-Nat.mul_succ_l. reflexivity.
                  unfold page_size , nb_pte.
                  simpl. omega.
                  rewrite min_l;trivial.
                  replace (length [val]) with 1;trivial.
                  replace page_size with nb_pte. 
                  replace nb_pte with page_size in *. 
                  omega. intuition. intuition.           
                  intuition. }
                { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. }
                { unfold memory_length in HData. intuition. }
                { apply mult_lt_compat_r.
                   - apply pagetable_position with s;intuition. 
                   - unfold page_size.  simpl. omega. }
                { apply mult_le_compat_r.
                  apply le_lt_or_eq_iff.
                  left. 
                  
                  unfold used_notZero in *.         
                  unfold page_notZero in *.
                  generalize (HU page x).
                  intros. 
                  apply H3.
                  assumption.
                  unfold process_used_pages.
                  simpl. right.
                  assumption. }
                { apply NNPP.   unfold not. intros H9.
                  assert (p1.(cr3_save) <> page) as HNUPage.
                    + generalize (HIso x p1 page).
                      intros.
                      apply H3 in H0;trivial.
                      - unfold not in *. intros. 
                        apply H0. unfold process_used_pages.
                        simpl. left. assumption.
                      - intuition. 
                      - unfold process_used_pages.
                        simpl. 
                        right. intuition.  
                    + unfold not in *.
                      apply HNUPage.
                      apply not_or_and in H9.
                      simpl in H9.  
                      destruct H9 as (H9 & H10).  
                      apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
                      unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                      apply not_le in H9. 
                      unfold process_used_pages. simpl. 
                      omega. } 
              * assumption. }         
      
  - unfold really_free in *. simpl.
    apply  really_free_freepage with x;intuition.
    unfold page_notZero in *.
    
    unfold used_notZero in *.
    generalize (HU page x).
    intros.
    unfold page_table_length.
    unfold page_table_length_aux.
    intros.
    apply pagetable_position with s;intuition.
 unfold used_notZero in *.
    generalize (HU page x).
    intros.
    
   
    apply H in Hx.
    intuition. 
    unfold process_used_pages. 
    simpl.
    unfold page_table_length.
    unfold page_table_length_aux.
    right.
    assumption.
         unfold Not_free.
    destruct (le_dec  nb_page s.(first_free_page)).
    constructor 1. intuition.
    apply not_le in n.
    apply used_page_not_free with s x page in HRFree .
    unfold Not_free in *. assumption.
    intuition.
    intuition.
    rewrite <- Hxcr3. assumption.
  - unfold not_cyclic in *. simpl in *. 
     destruct (le_dec nb_page s.(first_free_page)). 
      { constructor.  assumption. } 
      { inversion HRFree.
         + contradict H. intuition.
         + induction HNCyc.
           - contradict H. intuition.
           - constructor 2; trivial. inversion H1.
             * constructor . 
               unfold update_sublist. rewrite <- insert_pte_nth;intuition.
                { apply not_eq_and_le_lt;trivial.
                   +  unfold not. unfold all_cr3 in *.
                      intros.
                     apply H0. 
                     unfold all_used_pages. 
                     rewrite in_flat_map. 
                     exists x. 
                     split. assumption.
                     unfold process_used_pages. 
                     simpl. 
                     right. 
                     rewrite <- H5. assumption.  
              
                  + unfold page_size. simpl. omega. }
               { unfold page_notZero in *.
                 
                 unfold used_notZero in *.
                 generalize (HU page x).
                 intros.
                 apply H5 in Hx.
                 intuition. 
                 unfold process_used_pages. 
                 simpl. 
                 right.
                 assumption. }  
           * unfold update_sublist. rewrite <-insert_pte_nth;intuition.
              { unfold update_sublist in *.
                assert (pos <> page) as HNUPage.
                    + unfold not in *.
                      intros. 
                      apply H0.
                      unfold all_used_pages.
                      apply in_flat_map.
                      exists x.
                      split;trivial.
                      unfold process_used_pages.
                      simpl.
                      right.
                      rewrite H7.
                      assumption.
                    + apply NNPP.  unfold not in *.
                      intros H9.
                      apply HNUPage.
                      apply not_or_and in H9.
                      simpl in H9.  
                      destruct H9 as (H9 & H11).  
                      apply not_le in H11.
                      unfold page_size in H9. 
                      unfold page_size in H11.
                      unfold nb_pte in *.  
                      unfold offset_nb_bits in H11.
                      unfold offset_nb_bits in H9. 
                      simpl in H11 ,H9. 
                      apply not_le in H9. 
                      unfold process_used_pages. simpl. 
                      omega.  
                  }
                   
          {  unfold page_notZero in *.
             
             unfold used_notZero in *.
             generalize (HU page x).
             intros. 
             apply H7.
             assumption.
             unfold process_used_pages.
             simpl. right.
             assumption. } }
  -  unfold memory_length in *. Opaque page_size.
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
              + apply gt_le_S. intuition.

            unfold page_notZero in *.
            unfold used_notZero in *.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial. }
          { apply mult_succ_l. }
          { intuition. }
      * rewrite  <- HData.
        rewrite mult_comm.
        
            unfold page_notZero in *.
           
            unfold used_notZero in *.
           
            generalize (HU page x).
            intros.
        apply mult_le_compat_l.
                  apply le_lt_or_eq_iff.
                  left. 
                       apply H.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
       * unfold page_notZero in *.
         unfold used_notZero in *.
         generalize (HU page x).
         intros.
         apply H.
         assumption.
         unfold process_used_pages.
         simpl. right.
         assumption.
  - unfold noDuplic_processPages in *.
    intros.  Opaque update_sublist process_used_pages . simpl in *.
    Transparent update_sublist process_used_pages. 
   
    unfold process_used_pages in *.
    assert (
    get_mapped_pte p.(cr3_save) s.(data) = get_mapped_pte p.(cr3_save)
     (firstn (page * page_size) s.(data) ++
      update_sublist index val
        (sublist (page * page_size) nb_pte s.(data)) ++
      skipn (page * page_size + nb_pte) s.(data))).
      unfold get_mapped_pte.
      f_equal. f_equal.
      *  Transparent update_sublist. 
        unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn index
        (sublist (page * page_size) nb_pte s.(data)) ++
        [val] ++
        skipn (index + 1)
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
            unfold page_size. simpl. omega. 
             
            unfold page_notZero in *.
            
            unfold used_notZero in *.
            apply gt_le_S.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H0.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial.
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial.
               replace (length [val]) with 1;trivial.
               
               replace nb_pte with page_size in *;trivial.
               intuition. 
               replace nb_pte with page_size in *;trivial. intuition. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           { apply mult_lt_compat_r.
                + apply pagetable_position with s;intuition. 
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. 
              
            unfold page_notZero in *.
           

            unfold used_notZero in *.
                apply le_lt_or_eq_iff.
                  left. 
            generalize (HU page x).
            intros. 
            apply H0.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             destruct ( process_eq_dec x p).
              + assert (page <> p.(cr3_save)). 
                - 
                      unfold noDuplic_processPages in *. 
                      unfold page_notZero in *.
                      generalize (HNDup p).
                      intros.
                      apply H0 in H. 
                      unfold process_used_pages in *. 
                      simpl in H.
                      inversion H. 
                      rewrite <- e in H3.
                      unfold not.
                      unfold not in H3. 
                      intros. apply H3.
                      rewrite e at 1.
                      rewrite <- H5.
                      assumption.
               - unfold not in *.
                 apply H0.
                 apply not_or_and in H9.
                 simpl in H9.  
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10.
                 unfold page_size in H9.
                 unfold page_size in H10.  unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                 apply not_le in H9. 
                 unfold process_used_pages. simpl. 
                 omega. 
               + assert (page <> p.(cr3_save)). 
                -
              unfold noDuplic_processPages in *. 
              unfold page_notZero in *.            
              generalize (HIso x p page).
              intros.
              apply H0 in H;trivial.
               * unfold not in *. intros. 
                 apply H. unfold process_used_pages.
                 simpl. left. intuition. 
               * unfold process_used_pages.
                 simpl. 
                 right. intuition. 
               - unfold not in *.
                 apply H0.
                 apply not_or_and in H9.
                 simpl in H9.  
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10.
                 unfold page_size in H9.
                 unfold page_size in H10.  unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                 apply not_le in H9. 
                 unfold process_used_pages. simpl. 
                 omega. } 
        * replace nb_pte with page_size in *. rewrite <- H0. 
        apply HNDup;trivial.
          intuition.

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
          data := firstn (page * page_size) s.(data) ++
                  update_sublist index val
                    (sublist (page * page_size) page_size s.(data)) ++
                  skipn (page * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *.
 simpl in H.
        unfold page_notZero in *.
       
     unfold used_notZero in *.
     generalize (HU pg1 p1).
     intro HUp.  apply HUp;trivial.
     unfold process_used_pages in *.
    assert (
    get_mapped_pte p1.(cr3_save) s.(data) = get_mapped_pte p1.(cr3_save)
          (firstn (page * page_size) s.(data) ++
           update_sublist index val
             (sublist (page * page_size) page_size s.(data)) ++
           skipn (page * page_size + nb_pte) s.(data))).
      unfold get_mapped_pte.
     f_equal. f_equal.
      * Transparent update_sublist.

 unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn index
        (sublist (page * page_size) nb_pte s.(data)) ++
        [val] ++
        skipn (index + 1)
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
            unfold page_size. simpl. omega. 
             
            unfold page_notZero in *.

            unfold used_notZero in *.
            apply gt_le_S.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H1.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial.
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial.
               replace (length [val]) with 1;trivial.
               
               replace nb_pte with page_size in *;trivial.
               intuition. 
               replace nb_pte with page_size in *;trivial. intuition. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           { apply mult_lt_compat_r.
                + apply pagetable_position with s;intuition.
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. 
              
            unfold page_notZero in *.
            
            unfold used_notZero in *.
                apply le_lt_or_eq_iff.
                  left. 
            generalize (HU page x).
            intros. 
            apply H1.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             destruct ( process_eq_dec x p1).
              + assert (page <> p1.(cr3_save)). 
                - 
                      unfold noDuplic_processPages in *. 
                      unfold page_notZero in *.
                      generalize (HNDup p1).
                      intros.
                      apply H1 in H. 
                      unfold process_used_pages in *. 
                      simpl in H.
                      inversion H. 
                      rewrite <- e in H5.
                      unfold not.
                      unfold not in H4. 
                      intros. apply H4.
                      rewrite <- e at 2.
                      rewrite <- H6.
                      assumption.
               - unfold not in *.
                 apply H1.
                 apply not_or_and in H9.
                 simpl in H9.  
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10.
                 unfold page_size in H9.
                 unfold page_size in H10.  unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                 apply not_le in H9. 
                 unfold process_used_pages. simpl. 
                 omega. 
               + assert (page <> p1.(cr3_save)). 
                -
              unfold noDuplic_processPages in *. 
              unfold page_notZero in *.            
              generalize (HIso x p1 page).
              intros.
              apply H1 in H;trivial.
               * unfold not in *. intros. 
                 apply H. unfold process_used_pages.
                 simpl. left. intuition. 
               * unfold process_used_pages.
                 simpl. 
                 right. intuition. 
               - unfold not in *.
                 apply H1.
                 apply not_or_and in H9.
                 simpl in H9.  
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10.
                 unfold page_size in H9.
                 unfold page_size in H10.  unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                 apply not_le in H9. 
                 unfold process_used_pages. simpl. 
                 omega. }  
      * rewrite H1. apply H0;trivial.
  - 
   simpl ( {|
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
                  update_sublist index val
                    (sublist (page * page_size) page_size s.(data)) ++
                  skipn (page * page_size + nb_pte) s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *.
          simpl in H.
          unfold page_notZero in *.
            
          unfold used_notZero in *.
          generalize (HU pg1 p1).
          intro HUp.  apply HUp;trivial.
          unfold process_used_pages in *.
          assert (
          get_mapped_pte p1.(cr3_save) s.(data) = get_mapped_pte p1.(cr3_save)
          (firstn (page * page_size) s.(data) ++
          update_sublist index val
          (sublist (page * page_size) page_size s.(data)) ++
          skipn (page * page_size + nb_pte) s.(data))).
          unfold get_mapped_pte.
          f_equal. f_equal.
           * Transparent update_sublist.

           unfold update_sublist in *. 
        set (l1 := firstn (page* page_size) s.(data) ) in *. 
        set (l2 := skipn (page * page_size + nb_pte) s.(data)) in *.
        (*set (l3 := (sublist (page * page_size) nb_pte s.(data))) in *.
        set (page_sublist := (firstn 0 l3 ++ [s.(first_free_page)] ++ skipn (0 + 1) l3)).*)
        set (page_sublist := (firstn index
        (sublist (page * page_size) nb_pte s.(data)) ++
        [val] ++
        skipn (index + 1)
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
            unfold page_size. simpl. omega. 
             
            unfold page_notZero in *.

            unfold used_notZero in *.
            apply gt_le_S.
            replace (nb_page > page) with (page< nb_page).
            generalize (HU page x).
            intros. 
            apply H1.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption.
            trivial.
               rewrite <-Nat.mul_succ_l. reflexivity.
               unfold page_size , nb_pte.
               simpl. omega.
               rewrite min_l;trivial.
               replace (length [val]) with 1;trivial.
               
               replace nb_pte with page_size in *;trivial.
               intuition. 
               replace nb_pte with page_size in *;trivial. intuition. }
           { unfold nb_pte.  unfold base_virt_page__nb_bits. simpl.  omega. } 
           { unfold memory_length in HData. intuition. }
           { intros. apply mult_lt_compat_r.
                + apply pagetable_position with s;intuition.
                + unfold page_size.  simpl. omega. }
           { apply mult_le_compat_r. 
              
            unfold page_notZero in *.
            
            unfold used_notZero in *.
                apply le_lt_or_eq_iff.
                  left. 
            generalize (HU page x).
            intros. 
            apply H1.
            assumption.
            unfold process_used_pages.
            simpl. right.
            assumption. }
           { (*destruct H7 as (Hxp1 & Hxp2).*)
             apply NNPP.   unfold not in *. intros H9.
             destruct ( process_eq_dec x p1).
              + assert (page <> p1.(cr3_save)). 
                - 
                      unfold noDuplic_processPages in *. 
                      unfold page_notZero in *.
                      generalize (HNDup p1).
                      intros.
                      apply H1 in H. 
                      unfold process_used_pages in *. 
                      simpl in H.
                      inversion H. 
                      rewrite <- e in H5.
                      unfold not.
                      unfold not in H4. 
                      intros. apply H4.
                      rewrite <- e at 2.
                      rewrite <- H6.
                      assumption.
               - unfold not in *.
                 apply H1.
                 apply not_or_and in H9.
                 simpl in H9.  
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10.
                 unfold page_size in H9.
                 unfold page_size in H10.  unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                 apply not_le in H9. 
                 unfold process_used_pages. simpl. 
                 omega. 
               + assert (page <> p1.(cr3_save)). 
                -
              unfold noDuplic_processPages in *. 
              unfold page_notZero in *.            
              generalize (HIso x p1 page).
              intros.
              apply H1 in H;trivial.
               * unfold not in *. intros. 
                 apply H. unfold process_used_pages.
                 simpl. left. intuition. 
               * unfold process_used_pages.
                 simpl. 
                 right. intuition. 
               - unfold not in *.
                 apply H1.
                 apply not_or_and in H9.
                 simpl in H9.  
                 destruct H9 as (H9 & H10).  
                 apply not_le in H10.
                 unfold page_size in H9.
                 unfold page_size in H10.  unfold nb_pte in *.  
                 unfold offset_nb_bits in H10.
                 unfold offset_nb_bits in H9. simpl in H10 ,H9. 
                 apply not_le in H9. 
                 unfold process_used_pages. simpl. 
                 omega. }  
      * rewrite H1. apply H0;trivial.
 -unfold page_notZero in *. 
  
  unfold free_notZero in *. simpl. 
  unfold really_free in *. 

assert (page < nb_page).
unfold used_notZero  in *.
generalize (HU page x).
intros. 
apply H in Hx;intuition.
unfold process_used_pages. 
simpl. 
right. 
assumption.
apply free_not_zero_prop with x;trivial.
  - unfold currProcess_inProcessList in *.
    simpl in *.
    exists x;intuition. 
Qed. 


Lemma  write_invariant val Vaddr:
{{ fun (s : state) => isolation s.(data) s.(process_list) /\ consistent s }} 
  write val Vaddr 
{{ fun _  (s : state) => isolation s.(data) s.(process_list) /\ consistent s }}.
Proof. 
unfold write.
eapply bind_wp_rev.
 + eapply weaken. 
   - eapply translate_invariant.
   - intros. simpl. assumption.
 + intros. simpl.
   destruct a as [Paddr | ].
   eapply weaken.
   eapply write_aux_invariant.
   intros.
   simpl.
   split. 
   intuition.
   split. 
   intuition.
   destruct H as (H & H1 & H2).
   destruct H2 as (page & index & HPage & HPaddr & HIndex).
   exists page, index.
   repeat split;trivial.
   eapply weaken.
   eapply ret_wp.
   intros. 
   intuition.
Qed.

