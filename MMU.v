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

Require Import FunctionalExtensionality Bool List Streams Arith NPeano Omega.
Import List.ListNotations.
Require Import Lib StateMonad HMonad.

Set Printing Projections.

(** * Translation *)

Definition get_PTE_offset (virt_addr: nat) : M (nat * nat) :=
perform s := get in
let base := getBase virt_addr offset_nb_bits  in
let offset := getOffset virt_addr offset_nb_bits  in 
let idx := (s.(cr3)  * page_size) + base in 
perform PTE := nth idx s.(data) in 
ret (PTE , offset).


Lemma get_PTE_offset_wp (addr: nat) (P : (nat * nat)-> state -> Prop) :
{{ fun s => 
forall d , exists  base offset idx PTE  ,            
            (base = getBase  addr offset_nb_bits  )  /\ 
            (offset = getOffset addr offset_nb_bits    ) /\
            (idx = (s.(cr3) * page_size) + base /\
            (PTE = List.nth idx s.(data) d) /\
            (idx < length s.(data)) /\
            (P (PTE , offset) s))
}} get_PTE_offset addr  {{ P }}.
Proof.
repeat (eapply bind_wp; intros).
-eapply weaken.
  +eapply ret_wp.
  +instantiate (1 := fun _ s => P _ _). simpl. intros. eassumption.
-apply nth_wp .
-eapply weaken.
 +apply get_wp.
 +intros.
  split.
  *destruct ( H 0) as [ base G] .
   firstorder.
  *intros.
   destruct ( H d) as [ base G] .
   firstorder.
   congruence.
Qed.

Definition bit_to_bool (n:nat) : bool :=
  beq_nat n 1.
(*
match n with
|1 => true
| _ => false
end.
*)

Definition page_exist (PTE : nat ) : M (unit + exception) :=
let valid := getOffset PTE valid_bits in 
let b_valid := bit_to_bool valid in
if b_valid then  ret (inl tt) else ret (inr faultpage).

Lemma page_exist_wp ( PTE : nat) ( P : (unit + exception) -> state -> Prop ) :
{{ fun s : state =>
   exists (valid : nat) (b_valid : bool),
     valid = getOffset PTE valid_bits /\
     b_valid = bit_to_bool valid /\
     (b_valid = true /\ P (inl tt) s \/
      ((b_valid = false /\ P (inr faultpage) s ))  )}} page_exist PTE {{ P }}.
Proof.
unfold page_exist.
case_eq (bit_to_bool (getOffset PTE valid_bits)); intro H; simpl.
 -eapply weaken.
   +apply ret_wp.
   +intro.
     intro.
     firstorder.
     subst.
     congruence.
 -eapply weaken.
  apply ret_wp.
  intros.
  firstorder.
  subst.
  congruence.
Qed.

Definition get_access_permission (n : nat) : bool :=
  Nat.ltb 0 n.
(*
match n with 
|0 => false
| _ => true
end.
*)


Definition get_phyaddr( PTE offset: nat) : M (nat + exception):=
perform s := get in 
let newBasePhy := getBase PTE  (accesPermission_bits + valid_bits)  in  
let ap := get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits )in 
let phyaddr := shift_add newBasePhy offset offset_nb_bits  in
if  (ap || s.(kernel_mode)) then ret (inl phyaddr) else ret (inr noaccess).

Lemma get_phyaddr_wp ( PTE offset: nat) (P : (nat + exception) -> state -> Prop) :
{{ fun s : state =>
  (exists (newBasePhy : nat) (ap : bool) (phyaddr : nat),
     newBasePhy = getBase PTE (accesPermission_bits + valid_bits) /\
      ap = get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits ) /\
      phyaddr = shift_add newBasePhy offset offset_nb_bits /\
     ((ap = true \/ s.(kernel_mode) = true) /\ P (inl phyaddr) s \/
      ap = false /\ s.(kernel_mode) = false /\ P (inr noaccess) s)) (*\/ (forall excp , excp <> noaccess ->  P (inr excp) s )*) }} 
  get_phyaddr PTE offset {{ P }}.
Proof.
unfold get_phyaddr.
eapply bind_wp; intros.
-instantiate (1 := fun s s'=> 
  ((get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits) = true  \/ s.(kernel_mode) = true) /\ P (inl (shift_add (getBase PTE (accesPermission_bits + valid_bits)) offset offset_nb_bits)) s' ) \/
 (get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits ) = false /\ s.(kernel_mode) = false /\ P (inr noaccess) s' )).
 case_eq (get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits ) ).
 +intros.
  simpl.
  eapply weaken.
  *eapply ret_wp.
  *intros.
   firstorder.
  discriminate.
 +intros.
  simpl.
  case_eq (a.(kernel_mode)).
  *intros.
   eapply weaken.
   {eapply ret_wp. }
   intros.
   firstorder.
   discriminate.
 *intros.
  eapply weaken.
  {eapply ret_wp. }
  intros.  
  firstorder.
  {discriminate. }
  discriminate.
-eapply weaken .
 +eapply get_wp.
 +intros;
  firstorder.
  *subst.
   left.
   split.
   {left. assumption. }
   assumption.
  *subst.
   left.
   split.
   {right. assumption. }
   assumption.
  *subst.
   right.
   split.
   assumption.
  split.
    {assumption. }
{ assumption. }  
Qed.

Definition translate (addr : nat) : M (nat + exception) :=
if lt_dec addr  (Nat.pow 2 (offset_nb_bits + base_virt_page__nb_bits)) then 
  perform pte_offset := get_PTE_offset addr in 
  perform is_valid := page_exist (fst pte_offset) in 
  if is_valid then   
     get_phyaddr (fst pte_offset) (snd pte_offset) 
  else ret (inr faultpage)
else ret (inr noaccess).
 
Lemma translate_wp  (addr  : nat) ( P : (nat + exception) -> state -> Prop) :
{{ fun s : state =>
   forall d : nat,
   (addr < (Nat.pow 2 (offset_nb_bits + base_virt_page__nb_bits)) /\
   exists base offset idx PTE : nat,
     base = getBase addr offset_nb_bits  /\
     offset = getOffset addr offset_nb_bits  /\
     idx = (s.(cr3) * page_size) + base /\
     PTE = List.nth idx s.(data) d /\   
     idx < length s.(data) /\
     (exists (valid : nat) (b_valid : bool),
        valid = getOffset PTE valid_bits /\
        b_valid = bit_to_bool valid /\
        (b_valid = true /\
         (exists (newBasePhy : nat) (ap : bool) (phyaddr : nat),
            newBasePhy = getBase PTE (accesPermission_bits + valid_bits) /\
            ap = get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits ) /\
            phyaddr = shift_add newBasePhy offset offset_nb_bits /\
            ((ap = true \/ s.(kernel_mode) = true) /\ P (inl phyaddr) s \/
             ap = false /\ s.(kernel_mode) = false /\ P (inr noaccess) s) )
             \/
         b_valid = false /\ P (inr faultpage) s  )))
\/
(addr >= (Nat.pow 2 (offset_nb_bits + base_virt_page__nb_bits)) /\ P (inr noaccess) s)

 }} translate addr {{ P }}.
Proof.

unfold translate.
case_eq (lt_dec addr (2 ^ (offset_nb_bits + base_virt_page__nb_bits))).
intros l HV.
eapply bind_wp_rev.
- eapply weaken.
  + apply get_PTE_offset_wp.
  + simpl .
    intros s H d.
    generalize (H d); clear H; intro H.

    destruct H. 
    
    instantiate (1 := fun PTE_offset s => let PTE := fst PTE_offset in let offset := snd PTE_offset in
      (exists (valid : nat) (b_valid : bool),
         valid = getOffset PTE valid_bits /\
         b_valid = bit_to_bool valid /\
         (b_valid = true /\
          (exists (newBasePhy : nat) (ap : bool) (phyaddr : nat),
             newBasePhy = getBase PTE (accesPermission_bits + valid_bits) /\
             ap = get_access_permission (getOffset (getBase PTE valid_bits ) accesPermission_bits ) /\
             phyaddr = shift_add newBasePhy offset offset_nb_bits /\
             ((ap = true \/ s.(kernel_mode) = true) /\ P (inl phyaddr) s \/
              ap = false /\ s.(kernel_mode) = false /\ P (inr noaccess) s)) \/
          b_valid = false /\ P (inr faultpage) s))).
   simpl.
   destruct H.
    exact H0.
    simpl in l.
   destruct H. contradict H.
   intuition.
- intro PTE_offset.
  evar (P2 : unit + exception -> state -> Prop).
  evar (P1 : unit + exception -> state -> Prop).
  eapply bind_wp_rev.
   + simpl. eapply weaken.
    * eapply page_exist_wp.
    * intros s H.
      simpl.
      destruct H as (valid & b_valid & H1 & H2 & H).
      exists valid, b_valid.
      do 2 (split; try assumption).
      {destruct H as [H | H].
        - instantiate (1 := fun tt_or_excp s =>
            tt_or_excp = inl tt /\ P1 tt_or_excp s \/
            tt_or_excp = inr faultpage /\ P2 tt_or_excp s).
          unfold P1, P2. clear P1 P2.
          subst.
          instantiate (2 := fun tt_or_excp s =>
            bit_to_bool (getOffset (fst PTE_offset) valid_bits) = true /\
    (exists (newBasePhy : nat) (ap : bool) (phyaddr : nat),
       newBasePhy = getBase (fst PTE_offset) (accesPermission_bits + valid_bits) /\
       ap = get_access_permission (getOffset (getBase (fst PTE_offset) valid_bits) accesPermission_bits) /\
       phyaddr = shift_add newBasePhy (snd PTE_offset) offset_nb_bits /\
       ((ap = true \/ s.(kernel_mode) = true) /\ P (inl phyaddr) s \/
        ap = false /\ s.(kernel_mode) = false /\ P (inr noaccess) s))
          ).
          tauto.
- unfold P1, P2. clear P1 P2.
          subst.
          instantiate (1 := fun tt_or_excp s =>
            bit_to_bool (getOffset (fst PTE_offset) valid_bits) = false /\ P (inr faultpage) s
          ).
          tauto. }
    + unfold P1, P2. clear P1 P2.
      intros [ [] | excp].
      * eapply weaken.
        { apply get_phyaddr_wp. }
        { simpl.
          intros s [H | H].
          + firstorder.
          + intuition; discriminate. }
      * eapply weaken.
         { apply ret_wp. }
         { intros s [H | H].
          + intuition; discriminate.
          + tauto. }
- intros.
  
  eapply weaken.
         { apply ret_wp. }
         { intros.
           generalize (H0 0 ); clear H0; intro H0.
           destruct H0 as [(H0 & H2) | (H0 & H2)].
          + contradict H0. intuition.
          + tauto. }
Qed.


