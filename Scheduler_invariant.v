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
Require Import Lib StateMonad HMonad MMU Alloc_invariants
 Properties LibOs PageTableManager 
Scheduler MemoryManager.
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Definition default_process :=  
{| cr3_save := 0; eip:=0; process_kernel_mode := true ; stack_process := [] |} .

Definition default_stack := 
(false , 0).
(** * Process management *)

Definition update_process (c : process)(pc cr3: nat)  : process :=
{| cr3_save := cr3; eip:=pc; process_kernel_mode :=c.(process_kernel_mode) ; stack_process := c.(stack_process) |} .

Definition enqueuelist {A : Type} (l : list A) (a: A) : list A :=
l ++ [a].


Definition update_list_process (l :list process) : M unit :=
    modify (fun s => {|
  process_list := l;
  current_process := s.(current_process);
  code := s.(code) ;
  cr3 := s.(cr3);
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := s.(stack);
  register := s.(register);
  first_free_page := s.(first_free_page);
  data := s.(data) 

|}).

Lemma update_list_process_wp (l :list process) (P : unit -> state -> Prop) :
  {{ fun s => P tt {|
   process_list := l;
  current_process := s.(current_process);
   cr3 := s.(cr3);
  code := s.(code) ;
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := s.(stack);
  register := s.(register);
    first_free_page := s.(first_free_page);
  data := s.(data)    
  |}
}} update_list_process l {{ P }}.
Proof.
apply modify_wp.
Qed.

Definition save_process : M unit := 
perform s := get in(* get state*)
let process := s.(current_process) in (* get next process*)
let a := List.hd default_stack s.(stack) in 
let eip := snd a in
let new_process := update_process process eip s.(cr3)in 

let list_process := List.tl s.(process_list) in 
let l := enqueuelist list_process new_process in update_list_process l.

Lemma  save_process_wp (P : unit -> state -> Prop) :
  {{ fun s =>  P tt  {|
  process_list := enqueuelist (List.tl s.(process_list))
                    (update_process s.(current_process)
                       (snd (List.hd default_stack s.(stack))) s.(cr3));
  current_process := s.(current_process);
  cr3 := s.(cr3);
  code := s.(code);
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := s.(stack);
  register := s.(register);
  data := s.(data);
  first_free_page := s.(first_free_page) |}
}}
save_process
{{ P }}.
Proof.
unfold save_process.
eapply bind_wp.
 + intro s.
   eapply update_list_process_wp.
 + eapply weaken.
  eapply get_wp. 
  intros. 
  simpl.
  assumption.
Qed.


Definition restore_process : M unit :=
perform s := get in
let process := List.hd default_process s.(process_list) in
let h' := List.hd default_stack s.(stack) in 
let new_stack := List.tl s.(stack) in 
let km := process.(process_kernel_mode) in
let eip := process.(eip)in 
  modify (fun s => {|
  process_list := s.(process_list);
  current_process := process;
  cr3 := process.(cr3_save);
  intr_table := s.(intr_table);
  interruptions :=  s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := (km, eip)::new_stack;
  register := s.(register);
  data := s.(data) ;
  first_free_page := s.(first_free_page);
  code := s.(code)
|}).


Lemma  restore_process_wp  (P : unit -> state -> Prop) :
  {{ fun s => P tt
  {|
  process_list := s.(process_list);
  current_process := List.hd default_process s.(process_list);
  cr3 := (List.hd default_process s.(process_list)).(cr3_save);
  code := s.(code);
  intr_table := s.(intr_table);
  interruptions := s.(interruptions);
  kernel_mode := s.(kernel_mode);
  pc := s.(pc);
  stack := ((List.hd default_process s.(process_list)).(process_kernel_mode),
           (List.hd default_process s.(process_list)).(eip))
           :: List.tl s.(stack);
  register := s.(register);
  data := s.(data);
  first_free_page := s.(first_free_page) |}
}}
restore_process
{{ P }}.
Proof. 
unfold restore_process.
eapply bind_wp.
 + intro s. 
   eapply modify_wp. 
 + eapply weaken.
  eapply get_wp. 
  intros. 
  simpl.
  assumption.
Qed.

Lemma   all_used_pages_app :
forall s l p a, 
~ In a (all_used_pages s.(data) [p]) ->
~ In a (all_used_pages s.(data) l)-> 
~ In a (all_used_pages s.(data) (l ++ [p])).
Proof. 
intros. 
unfold all_used_pages. 
rewrite in_flat_map.
unfold not. intros.
destruct H1.
destruct H1.
unfold all_used_pages in *.
rewrite in_flat_map in *.
destruct H. 
apply NNPP. 
unfold not in *. 
intros. 
apply H0. 
exists x .
split.
 + apply in_app_iff in H1.
   destruct H1.
   assumption.
   contradict H.
   exists x.
   split.
   assumption.
   assumption.
 + assumption.
Qed.
  
Lemma really_free_save_process s l:
forall p, 
       really_free_aux [p] s.(data) s.(first_free_page) ->
       really_free_aux l s.(data) s.(first_free_page) ->
really_free_aux (l ++ [p]) s.(data) s.(first_free_page).
Proof.
intros.
inversion H.
 + constructor. assumption.
 + constructor 2. 
   - assumption. 
   - inversion H0. 
     contradict H4.
     intuition.
     clear H6 H3 H4 H0 H. 
     apply all_used_pages_app ;trivial.
   - induction H0. 
     contradict H1. intuition.
     inversion H3. 
     constructor .
     assumption. 
     constructor 2. 
     assumption. 
     inversion H5. 
     contradict H9. intuition.
     apply all_used_pages_app ;trivial.
     apply IHreally_free_aux;trivial.
Qed.      

Lemma really_free_aux_sublist data  l1 l2 pos :
really_free_aux l2 data pos  -> incl (all_used_pages data l1) (all_used_pages data l2) -> really_free_aux l1 data pos.
Proof.
intros H1 H2.
revert l1 H2.
induction H1; auto with *.
Qed.

Lemma save_process_invariant : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  }}
 save_process
{{ fun _ (s :state) => isolation s.(data) s.(process_list)  /\ consistent s }}.
Proof.
 eapply weaken.
 eapply save_process_wp.
 intros. 
 simpl. 
 split.
  + destruct H as (H & HCons). 
    unfold consistent in *. 
    destruct HCons as (HRFree & HNCyc & HData (* & HPTlen*) & HNdup & HNPzero & HCurp) .
    unfold  currProcess_inProcessList in *.
    destruct HCurp. 
    destruct H0.
    unfold update_process in *.
    simpl in *.
    unfold enqueuelist.
    rewrite <- H1.
    unfold isolation in *.
    intros. 
    apply in_app_or in H2. 
    apply in_app_or in H3.
    destruct H2 as [H2 | H2];
    destruct H3 as [H3 | H3].
    apply H with p1;trivial.
    simpl in *.
     - (*apply H with p1.*)    apply tl_In.    assumption.
     - apply tl_In. assumption.
     - unfold isolation in *.
       simpl in H3.
       destruct H3 as [ H3 | H3 ]; try tauto.
       subst p1.
       simpl in *.
       destruct H5 as [ H5 | H5 ].
        * apply H with x.   apply tl_In.    assumption. assumption. assumption.  left. assumption.
        *apply H with x.   apply tl_In.    assumption. assumption. assumption. right. assumption.
     - unfold isolation in *.
       simpl in H3.
       destruct H2 as [ H2 | H2 ]; try tauto.
       subst p2.
       simpl in *.
       destruct H5 as [ H5 | H5 ].
        * apply H with p1. assumption.   apply tl_In.    assumption. assumption.  left. assumption.
        *apply H with p1. assumption.   apply tl_In.    assumption. assumption. right. assumption.
    - contradict H4. simpl in H2 ,H3. intuition.
      rewrite <- H6. simpl. rewrite <- H2. simpl.
      trivial.
  + unfold consistent in *.
    try repeat split;trivial.
    - unfold really_free in *. 
      simpl.  destruct H as(HIso&  (HRFree & HNCyc & HData (* & HPTlen*) & HNdup & HNPzero) ).
      simpl in *.
      unfold enqueuelist. 
      assert(really_free_aux (List.tl s.(process_list)) s.(data)  s.(first_free_page)).
       * unfold List.tl in *.
         destruct s.(process_list).
         { assumption. }  
         { apply really_free_aux_sublist with (p :: l).
           assumption.
           assert ((all_used_pages s.(data) (p :: l)) =(all_used_pages s.(data) [p]) ++ all_used_pages s.(data) l).
            + unfold all_used_pages.
              unfold flat_map.
              rewrite app_nil_r.
              reflexivity.
            + rewrite H.
              apply incl_appr. 
              apply incl_refl. }
       * apply really_free_save_process.
         { unfold update_process. 
           simpl.      
           induction HRFree.
            + constructor. 
              assumption.
            + constructor 2.
              - assumption.
              - destruct HNPzero.
                unfold currProcess_inProcessList in *.
                destruct H3 as (p & Hp & Hpcr3).
                unfold all_used_pages in *. 
                unfold not in *. 
                intros. 
                apply H1. 
                apply in_flat_map.
                apply in_flat_map in H3.
                destruct H3. 
                exists p. 
                split. assumption.
                unfold process_used_pages in *. 
                simpl in *. 
                destruct H3.
                destruct H4.  
                left. 
                destruct H3;intuition. subst. simpl in *. assumption.
                right.
                destruct H3;intuition.
                subst. simpl in *.
                rewrite Hpcr3.  assumption.
              - apply IHHRFree.
                inversion H. 
                contradict H0.  intuition.
                assumption.  } 
        { assumption. }
  - unfold not_cyclic in *.
    simpl. intuition.
  - unfold memory_length.
    simpl.
    intuition. 
  - destruct H as(HIso&  (HRFree & HNCyc & HData (*& HPTlen*) & HNdup & HNPzero) ).
    unfold noDuplic_processPages in *.
    simpl.
    intros. 
    unfold enqueuelist in *.
    apply in_app_iff in H.
    destruct H.
    apply HNdup.
    unfold List.tl in *.
    destruct s.(process_list).
    assumption.
    intuition.
    unfold update_process in *.  simpl in *.
    destruct H;intuition. 
    unfold process_used_pages .
    rewrite <- H. simpl. 
    unfold currProcess_inProcessList in *.
    destruct H1. 
    generalize (HNdup x).
    intros. 
    destruct H1. 
    apply H2 in H1.
    unfold process_used_pages in H1.
    rewrite H3 in H1. 
    assumption. 
  - simpl in *.
    destruct H as(HIso&  (HRFree & HNCyc & HData (*& HPTlen*) & HNdup & HNPzero & Hcurp) ).
    unfold enqueuelist in *.
    apply in_app_iff in H0.
    unfold page_notZero in *.
    destruct HNPzero as (HU & HF).
    unfold used_notZero in *.
    destruct H1;destruct H0.
     * generalize (HU pg1 p1).
       intros.
       apply H1. 
       apply tl_In. assumption.
       unfold process_used_pages. 
       simpl. left. intuition. 
     * unfold update_process in *.
       rewrite <- H.
       simpl in H0. 
       destruct H0;trivial.
       subst.
       simpl in *.
       unfold currProcess_inProcessList in *.
       destruct Hcurp.
       generalize (HU s.(cr3) x).
       intros.
       apply H0. intuition.
       left. intuition.
       contradiction.
     * generalize (HU pg1 p1).
       intros.
       apply tl_In in H0.
       apply  H1 in H0. intuition.
       unfold process_used_pages.
       simpl. right. assumption.
     * unfold update_process in *.
       simpl in H0. destruct H0;intuition.
       contradict H1.
       unfold currProcess_inProcessList in *.
       destruct Hcurp as (p & Hp & Hpcr3).
       subst.
       simpl in *.
       generalize (HU pg1 p).
       intros.
       apply H0 in Hp.
       intuition.
       right.
       rewrite Hpcr3. 
       assumption.
  - simpl in *. destruct H as(HIso&  (HRFree & HNCyc & HData (* & HPTlen*) & HNdup & HNPzero & Hcurp) ).
    unfold enqueuelist in *.
    apply in_app_iff in H0.
    unfold page_notZero in *.
    destruct HNPzero as (HU & HF).
    unfold used_notZero in *.
    destruct H1;destruct H0.
     * generalize (HU pg1 p1).
       intros.
       apply H1. 
       apply tl_In. assumption.
       unfold process_used_pages. 
       simpl. left. intuition. 
     * unfold update_process in *.
       rewrite <- H.
       simpl in H0. 
       destruct H0;trivial.
       subst.
       simpl in *.
       unfold currProcess_inProcessList in *.
       destruct Hcurp.
       generalize (HU s.(cr3) x).
       intros.
       apply H0. intuition.
       left. intuition.
       contradiction.
     * generalize (HU pg1 p1).
       intros.
       apply tl_In in H0.
       apply  H1 in H0. intuition.
       unfold process_used_pages.
       simpl. right. assumption.
     * unfold update_process in *.
       simpl in H0. destruct H0;intuition.
       
       unfold currProcess_inProcessList in *.
       destruct Hcurp as (p & Hp & Hpcr3).
       subst.
       simpl in *.
       generalize (HU pg1 p).
       intros.
       apply H0 in Hp.
       intuition.
       right.
       rewrite Hpcr3. 
       assumption.
  - simpl. unfold page_notZero in *.
      unfold free_notZero in *.
      simpl.
      intuition.
  - unfold currProcess_inProcessList in *.
      simpl in *.
      destruct H as(HIso&  (HRFree & HNCyc & HData (*& HPTlen*) & HNdup & HNPzero & Hcurp) ).
      destruct Hcurp as (p & Hp & Hpcr3). 
      exists ({|
      eip := snd (List.hd default_stack s.(stack));
      process_kernel_mode := s.(current_process).(process_kernel_mode);
      cr3_save := s.(cr3);
      stack_process := s.(current_process).(stack_process) |} ) .
      split;trivial.
      unfold enqueuelist.
      apply in_or_app.
      right.
      unfold update_process.
      simpl.
      left.
      reflexivity.
Qed.

Lemma restore_process_invariant : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  }}
 restore_process
{{ fun _ (s :state) => isolation s.(data) s.(process_list)  /\ consistent s }}.
Proof.
 eapply weaken.
 eapply restore_process_wp.
 intros. 
 simpl.
 split.
 intuition. 
 unfold consistent in *.
 split;intuition.
 unfold currProcess_inProcessList in *.
 simpl.
destruct H6. 
exists (List.hd default_process s.(process_list)).
split.
unfold List.hd.
destruct (s.(process_list)).
intuition. intuition. reflexivity.
Qed.

Definition switch_process :=
  save_process ;; restore_process.

Lemma switch_process_invariant : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  }}
switch_process
{{ fun _ (s :state) => isolation s.(data) s.(process_list)  /\ consistent s }}.
Proof.
unfold switch_process.
eapply bind_wp.
intros.
apply restore_process_invariant.
apply save_process_invariant.
Qed. 