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
Properties LibOs PageTableManager MemoryManager ProcessManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Lemma free_page_not_used s page : 
page < nb_page -> really_free_aux s.(process_list) s.(data) page -> 
forall p , In p s.(process_list) -> ~ In page ([p.(cr3_save)]++ get_mapped_pte p.(cr3_save) s.(data)).
Proof.
intros.
inversion H0.
  + contradict H2. intuition.  
  + contradict H3.
    unfold all_used_pages. apply in_flat_map. exists p. 
    split.  assumption. assumption. 
Qed.
Lemma permut_or : 
forall P Q, P \/ Q-> Q \/ P.
Proof.
intros.
intuition.
Qed.  

(** really free new process prop **)
Lemma really_free_new_process s:
forall p1, Not_free s p1.(cr3_save) -> 
       get_mapped_pte p1.(cr3_save) s.(data) = [] -> 
       really_free_aux s.(process_list) s.(data) s.(first_free_page) ->
really_free_aux ( s.(process_list)++[p1]) s.(data) s.(first_free_page).
Proof.
intros.
inversion H.
 + constructor. assumption.
 + constructor 2. 
      - assumption. 
      - unfold all_used_pages. rewrite in_flat_map. unfold not. intros.
       destruct H5. destruct H5.
       rewrite in_app_iff in *.
       apply  permut_or  in H5. 
        destruct H5.
         * unfold process_used_pages in H6. contradict H6. simpl. unfold not. intros.
           destruct H6.
            { contradict H6.  subst. simpl in *. destruct H5; [| now contradict H5]. 
             subst.  assumption. }
            { inversion H1.  
              + contradict H7. intuition.
              + subst. simpl in *. destruct H5; [| now contradict H5]. 
             subst.  rewrite  H0 in H6. intuition. }
         * unfold process_used_pages in H6. contradict H6. 
           apply free_page_not_used.  assumption. assumption. assumption. 
      - induction H1.
         *  contradict H2. intuition.
         * destruct H6.
 { constructor . assumption. }
 { constructor 2.
   +  assumption. 
   + unfold all_used_pages. rewrite in_flat_map. 
     contradict H7. destruct H7. destruct H7. rewrite in_app_iff in H7.
     apply permut_or in H7.
       
     destruct H7. simpl in *. destruct H7; [| now contradict H7]. 
              subst x. unfold  process_used_pages in H9. rewrite H0 in H9. simpl in H9.
     destruct H9. destruct H4.  contradict H4. intuition. contradict H9.  assumption. contradict H7. 
     unfold all_used_pages. rewrite in_flat_map. exists x. 
     split. assumption. assumption.
   + apply IHreally_free_aux.
     - assumption.
     - inversion H4. contradict H9. intuition. assumption.
     - inversion H4. 
       * contradict H9. intuition. 
       *  assumption. }
Qed. 

Lemma init_zero_nth s new_cr3: 
forall pos,  (pos * page_size )<  (new_cr3 * page_size) \/  (new_cr3 * page_size) + page_size  <= (pos * page_size )->
 memory_length s ->  new_cr3 < nb_page ->
 (List.nth (pos * page_size) s.(data) nb_page) = (List.nth (pos * page_size)
     (init_zero (new_cr3 * page_size) page_size s.(data)) nb_page).
Proof. 
intros.
unfold init_zero. 
destruct H.
 + set (l1 := repeat page_size 0 ++ skipn (new_cr3 * page_size + page_size) s.(data)). 
   rewrite app_nth1. rewrite firstn_nth.  reflexivity.  assumption. 
   rewrite length_firstn_le. assumption.
   unfold memory_length in *. rewrite <- H0. rewrite mult_comm with page_size nb_page.
   apply mult_le_compat_r. intuition.

 + rewrite app_assoc. set (l1 := (firstn (new_cr3 * page_size) s.(data) ++ repeat page_size 0) ). 
   rewrite app_nth2.
    - rewrite skipn_nth.
      unfold l1. rewrite app_length. rewrite length_firstn_le.
       * rewrite repeat_length.
         rewrite Nat.add_sub_assoc.
           rewrite minus_plus. reflexivity.
           assumption.
       * unfold memory_length in *. rewrite <- H0. rewrite mult_comm with page_size nb_page.
         apply mult_le_compat_r. intuition.
    - unfold  l1. rewrite app_length.
      rewrite length_firstn_le.
       * rewrite repeat_length. auto with *.
       * unfold memory_length in *. rewrite <- H0. rewrite mult_comm with page_size nb_page.
         apply mult_le_compat_r. intuition.  
Qed.


Lemma Not_free_update_memory_prop new_cr3 s:
       memory_length s ->  new_cr3 < nb_page -> 
       Not_free_aux new_cr3  s.(data)  s.(first_free_page) ->       
Not_free_aux new_cr3 (init_zero (new_cr3 * page_size) page_size s.(data)) s.(first_free_page).
Proof.
intros Hdata Hcr3 H0 .
inversion H0 as [H3 | H3  H4 H5]. 
 + constructor. assumption. 
 + induction H0 as [pos H | pos H H6 Not_free]. 
      - contradict H. intuition.  
      - constructor 2.
        * assumption.
        * assumption.
        * inversion H5. 
          constructor. rewrite <- init_zero_nth;trivial.
          apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.
        
         rewrite <- init_zero_nth;trivial. apply IHNot_free;trivial .
          apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.
Qed.

Lemma init_zero_position s new_cr3: 
forall p, In p s.(process_list) -> 
 ~ In new_cr3 (all_used_pages s.(data) s.(process_list)) -> 
p.(cr3_save) * page_size + page_size <= new_cr3 * page_size \/
new_cr3 * page_size + page_size <= p.(cr3_save) * page_size.
Proof. 
intros p Hp HNusedCr3 . 
unfold all_used_pages in *.
rewrite in_flat_map in *. apply NNPP.
unfold not in *.
 intros H2. apply HNusedCr3. 
apply not_or_and in H2. simpl in H2. exists p.
split.
 + assumption.
 + destruct H2 as(H2 & H3). 
   apply not_le in H3. 
   unfold page_size ,offset_nb_bits in H3 , H2;simpl in H3, H2. 
   apply not_le in H2.
   replace (p.(cr3_save) * 16 + 16) with (S p.(cr3_save) * 16) in H2.
    - unfold process_used_pages. simpl. left. 
      apply Nat.mul_lt_mono_pos_r  in H2.
      apply and_gt_plus. split. omega. omega. omega. 
    - apply mult_succ_l.
Qed.


Lemma repeat_sublist_unchanged  :   
forall i j len l, len > 0 ->  nb_page * page_size <= length l ->   i < nb_page * page_size -> j <= nb_page * page_size-> 
( i + len <= j  \/ j + len <= i ) -> 
sublist i len l = sublist i len  (firstn j l ++ repeat len 0 ++ skipn (j + len) l).
Proof.
intros.
destruct H3. 

 + set (l2 := repeat len 0 ++ skipn (j + len) l).  rewrite sublist_firstn. rewrite sublist_app_le.
   - unfold sublist.  simpl.  rewrite firstn_skipn. rewrite firstn_skipn.
     rewrite firstn_firstn. rewrite Min.min_l.  reflexivity. auto with *.  
   - simpl. 
     unfold sublist. 
     simpl. rewrite firstn_length.
     simpl. rewrite Min.min_l. assumption. rewrite <- H0. assumption. 
 + rewrite sublist_two_app.
   - unfold sublist.
     rewrite skipn_skipn.
     rewrite firstn_length.
     rewrite repeat_length.
     rewrite Min.min_l.
      * rewrite Nat.add_sub_assoc.
        set (a := j+len). rewrite minus_plus. reflexivity.
        assumption.
      *  rewrite <- H0. assumption. 
   - rewrite app_length.  
     rewrite firstn_length.
     rewrite repeat_length.
     rewrite Min.min_l. auto with *. 
     rewrite <- H0. assumption.   
Qed. 


(**   MODIFICATION DE LA MEMOIRE : RAISONNEMENT SUR LES PAGES LIBRES
      (1) Toute modification de la m\u00e9moire ne doit pas changer la valeur des pages libres 
      *** Solution :   le cr3 est not_free 
                     ET 
                       la position des pages libres est un multiple de page_size
                     Et 
                       une table de page est maintenue sur une seule page  
                     Et 
                       les pages libres ne sont pas modifi\u00e9es
                     ET 
                       les pages utilis\u00e9es ne sont pas modifi\u00e9es
      (2) Modifier un PTE ->  modification de la m\u00e9moire + ajout d'une page dans all_used_pages 
      *** Solution : 
                       (1)
                     ET 
                       La valeur de PTE n'est plus une page libre

**)



Lemma really_free_init_zero_prop new_cr3 s:
page_table_length s -> 
memory_length s ->
new_cr3 < nb_page ->
Not_free s new_cr3 ->
~ In new_cr3 (all_used_pages s.(data) s.(process_list)) ->
  really_free_aux s.(process_list) s.(data)  s.(first_free_page)->
  really_free_aux s.(process_list) (init_zero (new_cr3 * page_size) page_size s.(data)) s.(first_free_page).
Proof.
intros HPTlen Hdata Hcr3 H10 H1 H0 .
inversion H10 as [H3 | H3  H4 H5]. 
 + constructor. assumption. 
 + induction H0 as [pos H | pos H H6 really_free]. 
      - contradict H. intuition.  
      - constructor 2.
        * assumption.
        * unfold all_used_pages in *. rewrite in_flat_map in *.
          unfold not in *. intros H7. apply H6. destruct H7 as (p & H7 & H8).
          exists p. split. assumption.
          apply in_sublist with (init_zero (new_cr3 * page_size) page_size s.(data)). 
           { unfold init_zero.
             rewrite repeat_sublist_unchanged with  (p.(cr3_save) * page_size) (new_cr3 * page_size)  nb_pte s.(data).
              + unfold sublist. unfold nb_pte. unfold base_virt_page__nb_bits.
                unfold page_size.  unfold offset_nb_bits. reflexivity.
              + unfold nb_pte. unfold base_virt_page__nb_bits. simpl. auto with *.
              + unfold memory_length in Hdata. intuition.
              + unfold page_table_length in HPTlen. unfold page_table_length_aux in HPTlen.
                apply mult_lt_compat_r. apply HPTlen. assumption. unfold page_size. simpl. omega.
              +apply mult_le_compat_r. intuition. 
             
              + apply init_zero_position with s;trivial.  
             rewrite <- in_flat_map in H1. assumption. }
        { assumption. }
       * inversion H5. constructor. rewrite <- init_zero_nth;trivial. 
         apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega. 
         rewrite <- init_zero_nth;trivial. apply IHreally_free;trivial .

          apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.
Qed.


Lemma add_new_process_invariant (cr3 eip_: nat) :(** *la page (cr3_p) n'est plus libre & 
                                                 n'est pas encore attribu\u00e9e a un process* **)
{{ fun s :state => isolation s.(data) s.(process_list) /\ consistent s /\
                   ~ In cr3 (all_used_pages s.(data) s.(process_list)) /\ 
                   Not_free s cr3  /\ 
                   any_mapped_page s cr3 /\ 
                   cr3 < nb_page /\ cr3 <> 0}} 
 add_new_process cr3 eip_
{{fun _ (s: state) =>  isolation s.(data) s.(process_list)  /\ consistent s 
(** *la page (cr3_p) est attribu\u00e9e a un process* **)}}.
Proof.
eapply weaken; [apply add_new_process_wp | idtac].
simpl. unfold consistent, not_cyclic, really_free. simpl in *.
intros s (HIso & (HRFree  & HNCyc & HData (*& HPTlen*) & HNdup & HPNzero) & HNUsed & HNFree & HMPage & HPTlenCr3 & HCr3n0 ).
try repeat split;trivial.
+ unfold isolation. intros p1 p2 pg1 H H0 H1 H2 H3.
rewrite in_app_iff in *.
assert (Hi : In p2 [{| eip := eip_; process_kernel_mode := false; cr3_save := cr3; stack_process := [] |}] 
\/ In p2 s.(process_list)
    ) by intuition.
    clear H.
assert(Hi0 : In p1 [{| eip := eip_; process_kernel_mode := false; cr3_save := cr3; stack_process := [] |}]
\/  In p1 s.(process_list) ) by intuition.
clear H0. 
  destruct Hi0 as [H0|H0]; destruct Hi as [H| H].
  - simpl in *. clear H3 H2. intuition.
    contradict H1. subst. simpl;trivial. 
  - unfold process_used_pages in H2. unfold process_used_pages. unfold not. intros. destruct H2.
     * subst. simpl in *.
       destruct H3 as [H3 |H3].
       {contradict H3. apply not_eq_sym. assumption. }
       {   destruct HNUsed. unfold all_used_pages. apply in_flat_map.  exists p2. 
            split. assumption. unfold process_used_pages. apply in_or_app. right. 
            intuition. subst. simpl in *. assumption. }
     * replace ( get_mapped_pte p1.(cr3_save) s.(data)) with ( []: list nat) in H2 . 
       { contradict H2. }
       { simpl in H0. destruct H0 as [H0 | H0] ; [| now contradict H0].
         simpl in H2.  unfold any_mapped_page in HMPage . unfold get_mapped_pte in H2. subst.
         simpl in *. rewrite HMPage in H2. unfold get_mapped_pte. symmetry. assumption. }
  - unfold process_used_pages in H2. unfold process_used_pages. unfold not. intros. destruct H2.
     * subst. simpl in *.
       destruct H3 as [H3 |H3].
       {contradict H3. apply not_eq_sym. assumption. }
       { destruct H as [H | H] ; [| now contradict H].
         destruct HNUsed.
          unfold all_used_pages. apply in_flat_map.  exists p1. 
            split. assumption. unfold process_used_pages.
             apply in_or_app. right.  
            unfold any_mapped_page in HMPage . unfold get_mapped_pte in H3. 
            subst. simpl in *. 
            rewrite HMPage in H3. contradict H3. }
     * unfold process_used_pages in H3. simpl in H3. destruct H3 as [H3 |H3].
       { subst.  simpl in *. destruct H as [H | H] ; [| now contradict H].
        contradict HNUsed . unfold all_used_pages. apply in_flat_map.  exists p1. 
            split. assumption. unfold process_used_pages. apply in_or_app. right.  
            unfold any_mapped_page in HMPage . subst. simpl.  assumption. }
       { subst. simpl in *. destruct H as [H | H] ; [| now contradict H]. 
         unfold get_mapped_pte in H3. unfold any_mapped_page in HMPage.
         subst. simpl in *. 
         rewrite HMPage in H3. contradict H3. }
   - contradict H3.  unfold isolation in *. apply HIso with p1; trivial.
 + apply really_free_new_process. simpl . assumption. simpl. unfold get_mapped_pte . assumption. 
   assumption.
 + unfold noDuplic_processPages in *. simpl.
   intros.
   rewrite in_app_iff in H.
   apply permut_or in H. 
   simpl in H. 
   destruct H.
    *  destruct H as [H | H] ; [| now contradict H].  
      unfold  any_mapped_page in *.
      unfold process_used_pages. simpl. 
      unfold get_mapped_pte. 
      replace p.(cr3_save) with cr3;intuition.
      
      rewrite HMPage. constructor. intuition. 
      apply NoDup_nil. destruct H.  simpl.  trivial.  
    *   intuition.
    
 + simpl {|
      process_list :=  s.(process_list) ++
                          [{|
                           eip := eip_;
                           process_kernel_mode := false;
                           cr3_save := cr3;
                           stack_process := [] |}];
      current_process := s.(current_process);
      cr3 := s.(HMonad.cr3);
      code := s.(code);
      intr_table := s.(intr_table);
      interruptions := s.(interruptions);
      kernel_mode := s.(kernel_mode);
      pc := s.(pc);
      stack := s.(stack);
      register := s.(register);
      data := s.(data);
      first_free_page := s.(first_free_page) |}.(process_list)   in *.
      simpl  (process_used_pages
          {|
          process_list :=  s.(process_list) ++
                          [{|
                           eip := eip_;
                           process_kernel_mode := false;
                           cr3_save := cr3;
                           stack_process := [] |}];
          current_process := s.(current_process);
          cr3 := s.(HMonad.cr3);
          code := s.(code);
          intr_table := s.(intr_table);
          interruptions := s.(interruptions);
          kernel_mode := s.(kernel_mode);
          pc := s.(pc);
          stack := s.(stack);
          register := s.(register);
          data := s.(data);
          first_free_page := s.(first_free_page) |}.(data) p1) in *. 
   unfold used_notZero.
   simpl. intros. 
    unfold page_notZero in HPNzero.

    destruct HPNzero as ( HUNzero & HFNzero).
    unfold used_notZero in *.
    rewrite in_app_iff in H.
    apply permut_or in H.  
    destruct H as [H | H]; destruct H0 as [H0 | H0].
     - simpl in *. destruct H;[|now contradict H].  subst. simpl. assumption.
     -  simpl. simpl in *. destruct H;[|now contradict H].
       unfold any_mapped_page in HMPage.
        subst.  simpl in H0. unfold  get_mapped_pte in H0. 
         rewrite HMPage in H0. 
         contradict H0.
     - apply HUNzero with p1;trivial.
       unfold process_used_pages.
       simpl. 
       left. assumption.
     -  apply HUNzero with p1;trivial.
        unfold process_used_pages.
        simpl. right. trivial.
 + simpl in *.
     unfold page_notZero in HPNzero.
   rewrite in_app_iff in H.
   apply permut_or in H.
      

    destruct H as [H | H]; destruct H0 as [H0 | H0].
     - destruct H;[|now contradict H]. subst. simpl.  
       assumption.
     - destruct H;[|now contradict H]. subst.  simpl. unfold any_mapped_page in HMPage.
        subst.  simpl in H0. unfold  get_mapped_pte in H0. 
         rewrite HMPage in H0. 
         contradict H0.
     -  destruct HPNzero as ( HUNzero & HFNzero).
        apply HUNzero with p1;trivial.
       unfold process_used_pages.
       simpl. 
       left. assumption.
     -  destruct HPNzero as ( HUNzero & HFNzero).
       apply HUNzero with p1;trivial.
        unfold process_used_pages.
        simpl. right. trivial.
+ simpl.
    destruct HPNzero as (( HUNzero & HFNzero) & Hcurp).
     unfold free_notZero in *. simpl. assumption.
+   destruct HPNzero as (( HUNzero & HFNzero) & Hcurp).
     unfold currProcess_inProcessList in *. 
     simpl.
     destruct Hcurp as (x & HCurx).
     case_eq (beq_nat x.(cr3_save) s.(HMonad.cr3)). 
     intros. 
     apply beq_nat_true in H.
     exists x.
     intros. 
     split.
     rewrite in_app_iff.
     left.  
     intuition.  assumption.   
     intros. 
     apply beq_nat_false in H.
     exists {|
     eip := x.(eip);
     process_kernel_mode := x.(process_kernel_mode);
     cr3_save := s.(HMonad.cr3);
     stack_process := x.(stack_process) |}.
     split.
     apply in_app_iff.
     left.     destruct HCurx.
     rewrite <- H1.
     replace {|
  eip := x.(eip);
  process_kernel_mode := x.(process_kernel_mode);
  cr3_save := x.(cr3_save);
  stack_process := x.(stack_process) |} with x. assumption.
  intuition.
     intuition.
Qed.

Lemma free_not_zero_prop s page pos :
memory_length s ->
page < nb_page ->
Not_free_aux page s.(data) pos ->
 Free_notZero_aux s.(data) pos ->
Free_notZero_aux
  (init_zero (page * page_size) page_size s.(data)) pos.
Proof.
intros HData HP HNFree HF. 
induction HF.
constructor. 
assumption.
constructor 2.
assumption. assumption.
fold init_zero.
rewrite <- init_zero_nth;trivial. 
apply IHHF. 
inversion HNFree.
constructor.
contradict H1. intuition. 
assumption.
inversion HNFree. 
contradict H1.
intuition. 
apply not_eq_and_le_lt;trivial.
unfold page_size. simpl.
omega.
Qed.

Lemma init_process_page_table_invariant new_cr3:
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s /\
                  ~ In new_cr3 (all_used_pages s.(data) s.(process_list)) /\ 
                  Not_free s new_cr3  /\
                  new_cr3  < nb_page /\
                  new_cr3 <> 0}} 
  init_process_page_table new_cr3
{{fun _ (s: state) => isolation s.(data) s.(process_list)  /\ consistent s /\ 
                      ~ In new_cr3 (all_used_pages s.(data) s.(process_list)) /\ 
                      Not_free s new_cr3 /\  any_mapped_page s new_cr3 /\ 
                       new_cr3  < nb_page /\ new_cr3 <> 0}}.

Proof.
eapply weaken.
 + apply init_process_page_table_wp .
 + intros.  simpl. unfold consistent in H.  destruct H as (HIso & HCons & HNUCr3 & HNFreeCr3 & HCr3 & Hcr3zero ). 
   try repeat split.
    - unfold isolation in *. intros. 
      apply not_in_sublist with  s.(data) .
      * unfold init_zero.   destruct HCons as(HRfree &HNCyc & Hdata (*& HPTlen*)
       & HNdup).
        rewrite repeat_sublist_unchanged with  (p2.(cr3_save) * page_size) (new_cr3 * page_size)  nb_pte s.(data).
        { unfold sublist. unfold nb_pte. unfold base_virt_page__nb_bits.   
 	unfold page_size.  unfold offset_nb_bits. reflexivity. }
        { unfold nb_pte. simpl.  omega. }
        { unfold memory_length in Hdata. intuition. }
        { apply mult_lt_compat_r.
          + apply pagetable_position with s;intuition. 
            unfold page_notZero in *.
            intuition.
          + unfold page_size.  simpl. omega. }
        {  apply mult_le_compat_r. intuition. }
 	unfold all_used_pages in HNUCr3. simpl.  
 	apply NNPP.   unfold not in *. intros H9. apply HNUCr3.  apply in_flat_map.  
 	apply not_or_and in H9. simpl in H9. exists p2. split. assumption.  
 	destruct H9 as (H9 & H10).  
 	apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
 	unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
 	apply not_le in H9. 
 	unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. 
   
      * generalize (HIso p1 p2 pg1 ). intros H9. clear HIso. apply H9;trivial.
         clear H9. apply in_sublist with (init_zero (new_cr3 * page_size) page_size s.(data))  .
          { unfold init_zero. destruct HCons as(HRfree &HNCyc & Hdata & HPTlen & HNdup);unfold  page_table_length in HPTlen.

            unfold memory_length in Hdata. unfold  page_table_length in HPTlen.  
            unfold page_table_length_aux in HPTlen.
            apply repeat_sublist_unchanged .
             + unfold page_size.  simpl. omega. 
             + intuition. 
             + apply mult_lt_compat_r.
                - apply pagetable_position with s;intuition.
                  unfold page_notZero in *.
                  intuition.
                -  unfold page_size. simpl. omega. 
             + intuition. apply mult_le_compat_r. intuition.
             +
            unfold all_used_pages in HNUCr3.
            rewrite in_flat_map in HNUCr3. apply NNPP.   unfold not in *. intro HNor. apply HNUCr3. 
            apply not_or_and in HNor. simpl in HNUCr3. exists p1. split. assumption. 
            destruct HNor as (HNor_l & HNor_r). 
            apply not_le in HNor_r.  apply not_le in HNor_l. unfold page_size in HNor_l. unfold page_size in HNor_r.
            unfold offset_nb_bits in HNor_l. unfold offset_nb_bits in HNor_r. simpl in HNor_l , HNor_r.
            replace (p1.(cr3_save) * 16 + 16) with (S p1.(cr3_save) * 16) in HNor_l.
            unfold process_used_pages. simpl. left.  
            apply Nat.mul_lt_mono_pos_r  in HNor_l.  apply and_gt_plus. split.
            omega. omega. omega. 
            apply mult_succ_l. }
          { assumption. }
   - unfold really_free in *. simpl in *. apply really_free_init_zero_prop ;intuition.
     unfold page_table_length. unfold page_table_length_aux. 
     intros. unfold page_notZero in *. 
     apply pagetable_position with s;intuition. 
    
   - unfold not_cyclic in *. simpl in *. 
     destruct HCons as(HRfree &HNCyc & Hdata & HPTlen & HNdup);unfold  page_table_length in HPTlen.
     inversion HNFreeCr3.  constructor.  assumption. 
     induction HNCyc as [ page seen Hpageval | page seen Hpageval HNotSeen HNextCyc]. contradict H. intuition. 
     constructor 2;trivial. inversion H1. 
     constructor . rewrite <- init_zero_nth;trivial. 
     apply not_eq_and_le_lt;trivial. unfold page_size. simpl. omega.  
      *  rewrite <- init_zero_nth;trivial. apply IHHNextCyc;trivial.
        apply not_eq_sym in H0.  apply not_eq in H0.
        destruct H0.
         { left. apply Nat.mul_lt_mono_pos_r. unfold page_size. simpl. omega. assumption. } 
         { right.  auto with *.
           replace (new_cr3  * page_size + page_size) with (S new_cr3 * page_size).
            + apply Nat.mul_le_mono_pos_r . unfold page_size. simpl. omega. apply gt_le_S. assumption.
            + apply mult_succ_l. }
   - unfold memory_length in *.
   destruct HCons as(HRfree &HNCyc & Hdata (*& HPTlen*) & HNdup). 
   
     simpl. unfold init_zero. 
     rewrite app_length. rewrite app_length.
     rewrite firstn_length.     
     rewrite Min.min_l.
      * rewrite skipn_length. rewrite repeat_length.
        
        rewrite plus_assoc. 
        rewrite <- le_plus_minus with (new_cr3 * page_size + page_size) (length s.(data)).
        rewrite Hdata. intuition. 
        rewrite <- Hdata.  
        replace (new_cr3  * page_size + page_size) with (S new_cr3 * page_size).
         { rewrite  mult_comm with page_size nb_page.
             apply Nat.mul_le_mono_pos_r .
             + simpl. unfold page_size. unfold page_size. simpl. omega.
             + apply gt_le_S. intuition. }
         { apply mult_succ_l. }
      * 
        rewrite <- Hdata. rewrite  mult_comm with page_size nb_page. 
        apply Nat.mul_le_mono_pos_r . unfold page_size. simpl. omega. intuition. 
   - destruct HCons as(HRfree &HNCyc & Hdata (*& HPTlen *) & HNdup & hpnZERO).

     unfold noDuplic_processPages in *.
     intros.  Opaque update_sublist process_used_pages . simpl in *. Transparent update_sublist process_used_pages. 
     unfold all_used_pages in HNUCr3.
     rewrite in_flat_map in HNUCr3.
     unfold process_used_pages in *.
     assert (
     get_mapped_pte p.(cr3_save) s.(data)=
     get_mapped_pte p.(cr3_save)
     (init_zero (new_cr3 * page_size) page_size s.(data))).
      unfold get_mapped_pte.
     f_equal. f_equal.
      *Transparent update_sublist. 
        unfold update_sublist in *. 
        unfold init_zero.

        rewrite repeat_sublist_unchanged with  (p.(cr3_save) * page_size) (new_cr3 * page_size)  nb_pte s.(data).
        { unfold sublist. unfold nb_pte. unfold base_virt_page__nb_bits.   
 	  unfold page_size.  unfold offset_nb_bits. reflexivity. }
        { unfold nb_pte. simpl.  omega. }
        { unfold memory_length in Hdata. intuition. }
        { apply mult_lt_compat_r.
          + apply pagetable_position with s;intuition.
            unfold page_notZero in *. intuition. 
          + unfold page_size. simpl. omega. }
        { apply mult_le_compat_r. intuition. }
      unfold all_used_pages in HNUCr3. simpl.  
 	apply NNPP.   unfold not in *.
        intros H9. apply HNUCr3. apply in_flat_map.  
 	apply not_or_and in H9. simpl in H9. rewrite in_flat_map.
        exists p. split. assumption.  
 	destruct H9 as (H9 & H10).  
 	apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
 	unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
 	apply not_le in H9. 
 	unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega.
      * rewrite <- H0. apply HNdup;trivial.
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
          data := init_zero (new_cr3 * page_size) page_size s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *. simpl in H.
      
     destruct HCons as(HRfree &HNCyc & Hdata (*& HPTlen *)& HNdup & hpnZERO).
     unfold page_notZero in *.
     destruct hpnZERO as ((HU & HF) & Hpro). 
     unfold used_notZero in *.
     generalize (HU pg1 p1).
     intro HUp.  apply HUp;trivial.
     unfold process_used_pages in *.
     assert (
     get_mapped_pte p1.(cr3_save) s.(data)=
     get_mapped_pte p1.(cr3_save)
     (init_zero (new_cr3 * page_size) page_size s.(data))).
      unfold get_mapped_pte.
     f_equal. f_equal.
      * Transparent update_sublist. 
        unfold update_sublist in *. 
        unfold init_zero.

        rewrite repeat_sublist_unchanged with  (p1.(cr3_save) * page_size) (new_cr3 * page_size)  nb_pte s.(data).
        { unfold sublist. unfold nb_pte. unfold base_virt_page__nb_bits.   
 	  unfold page_size.  unfold offset_nb_bits. reflexivity. }
        { unfold nb_pte. simpl.  omega. }
        { unfold memory_length in Hdata. intuition. }
        { apply mult_lt_compat_r.
          + apply pagetable_position with s;intuition.
          + unfold page_size. simpl. omega. }
        { apply mult_le_compat_r. intuition. }
      unfold all_used_pages in HNUCr3. simpl.  
 	apply NNPP.   unfold not in *.
        intros H9. apply HNUCr3. apply in_flat_map.  
 	apply not_or_and in H9. simpl in H9.        
        exists p1. split. assumption.  
 	destruct H9 as (H9 & H10).  
 	apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
 	unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
 	apply not_le in H9. 
 	unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega.
      * rewrite H1. apply H0;trivial.
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
          data := init_zero (new_cr3 * page_size) page_size s.(data);
          first_free_page := s.(first_free_page) |}.(data)) in *. simpl in H.
      
     destruct HCons as(HRfree &HNCyc & Hdata (*& HPTlen *) & HNdup & hpnZERO).
     unfold page_notZero in *.
     destruct hpnZERO as ((HU & HF) & Hcurp). 
     unfold used_notZero in *.
     generalize (HU pg1 p1).
     intro HUp.  apply HUp;trivial.
     unfold process_used_pages in *.
     assert (
     get_mapped_pte p1.(cr3_save) s.(data)=
     get_mapped_pte p1.(cr3_save)
     (init_zero (new_cr3 * page_size) page_size s.(data))).
      unfold get_mapped_pte.
     f_equal. f_equal.
      * Transparent update_sublist. 
        unfold update_sublist in *. 
        unfold init_zero.

        rewrite repeat_sublist_unchanged with  (p1.(cr3_save) * page_size) (new_cr3 * page_size)  nb_pte s.(data).
        { unfold sublist. unfold nb_pte. unfold base_virt_page__nb_bits.   
 	  unfold page_size.  unfold offset_nb_bits. reflexivity. }
        { unfold nb_pte. simpl.  omega. }
        { unfold memory_length in Hdata. intuition. }
        { apply mult_lt_compat_r.
          + apply pagetable_position with s;intuition. 
          + unfold page_size. simpl. omega. }
        { apply mult_le_compat_r. intuition. }
      unfold all_used_pages in HNUCr3. simpl.  
 	apply NNPP.   unfold not in *.
        intros H9. apply HNUCr3. apply in_flat_map.  
 	apply not_or_and in H9. simpl in H9.        
        exists p1. split. assumption.  
 	destruct H9 as (H9 & H10).  
 	apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
 	unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
 	apply not_le in H9. 
 	unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega.
      * rewrite H1. apply H0;trivial. 
   - 
     unfold page_notZero in *.
unfold free_notZero in *. simpl.
destruct HCons as (HRFree & HNCyc & HData (*& HPTlen*) & HNDup &  (HU & HF) & Hcurp).
unfold init_zero.
unfold Not_free in *. 
apply free_not_zero_prop;trivial.
- unfold currProcess_inProcessList in *.
  simpl in *.
  intuition. 
   - unfold all_used_pages in *. rewrite in_flat_map in *. unfold not in *. intros. apply HNUCr3.
     destruct H. exists x. destruct H. split. assumption.
     apply in_sublist with (init_zero (new_cr3 * page_size) page_size s.(data)). 
      * unfold init_zero.
        destruct HCons as(HRfree &HNCyc & Hdata & HPTlen & HNdup);unfold  page_table_length in HPTlen.
        rewrite repeat_sublist_unchanged with  (x.(cr3_save) * page_size) (new_cr3 * page_size)  nb_pte s.(data).
        { unfold sublist. unfold nb_pte. unfold base_virt_page__nb_bits.   
 	  unfold page_size.  unfold offset_nb_bits. reflexivity. }
        { unfold nb_pte. simpl.  omega. }
        { unfold memory_length in Hdata. intuition. }
        { apply mult_lt_compat_r.
          + apply pagetable_position with s;intuition.
            unfold page_notZero in *.
            intuition. 
          + unfold page_size. simpl. omega. }
        { apply mult_le_compat_r. intuition. }
      unfold all_used_pages in HNUCr3. simpl.  
 	apply NNPP.   unfold not in *.
        intros H9. apply HNUCr3. apply in_flat_map.  
 	apply not_or_and in H9. simpl in H9. rewrite in_flat_map.
        exists x. split. assumption.  
 	destruct H9 as (H9 & H10).  
 	apply not_le in H10. unfold page_size in H9. unfold page_size in H10.  unfold nb_pte in *.  
 	unfold offset_nb_bits in H10. unfold offset_nb_bits in H9. simpl in H10 ,H9. 
 	apply not_le in H9. 
 	unfold process_used_pages. simpl. left. apply and_gt_plus. split; omega. 
      * assumption.
   - unfold Not_free in *. simpl in *.
     destruct HCons as(HRfree &HNCyc & Hdata & HPTlen & HNdup);unfold  page_table_length in HPTlen.
     
     apply Not_free_update_memory_prop;trivial.
   - destruct HCons as(HRfree &HNCyc & Hdata & HPTlen & HNdup);unfold  page_table_length in HPTlen.
     simpl. unfold  any_mapped_page .
     simpl. unfold init_zero.
     set(start:= new_cr3 * page_size).
     rewrite sublist_eq_two_app.
      { unfold nb_pte .
        unfold offset_nb_bits ,base_virt_page__nb_bits.
        rewrite sublist_zero_app_eq .
         + simpl. reflexivity.
         + auto with *. }
      { rewrite firstn_length.
        unfold memory_length in Hdata.
        unfold start.
        rewrite Min.min_l.
         + reflexivity.
         + rewrite <- Hdata. rewrite mult_comm with page_size nb_page. apply mult_le_compat_r.
           intuition. 
        } 
    - intuition. 
    - assumption.
Qed. 

Lemma create_process_invariant eip: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s}}
 create_process eip
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
unfold create_process .
eapply bind_wp_rev.  eapply alloc_page_invariant.
intros [ page |[] ].
 + eapply bind_wp_rev. 
   - eapply init_process_page_table_invariant.
   - intros []. eapply add_new_process_invariant.
 + eapply weaken. apply ret_wp. intros;trivial. simpl. intuition. 
Qed.

Lemma init_current_process_invariant: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s}}
 init_current_process 
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
unfold  init_current_process. simpl. 
 eapply weaken.  eapply modify_wp.
 intros. 
  simpl. intuition. unfold consistent in *. 
  simpl in *. intuition. 
  unfold currProcess_inProcessList in *.
  simpl in *.
  destruct H6.
  exists (List.hd
   {|
   eip := 0;
   process_kernel_mode := false;
   cr3_save := 0;
   stack_process := [] |} s.(process_list)).
  intuition.

  induction s.(process_list).
  simpl. contradict H6.
  simpl in *.
  left. reflexivity. 
Qed.

