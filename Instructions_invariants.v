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
Require Import Lib StateMonad HMonad MMU Alloc_invariants Properties LibOs
 PageTableManager MemoryManager 
Instructions MMU_invariant ProcessManager_invariant ProcessManager .
Require Import Coq.Structures.OrderedTypeEx.

Set Printing Projections.

Lemma fetch_interruption_invariant: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s}}
fetch_interruption
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
eapply weaken.
eapply fetch_interruption_wp.
intros.
simpl. 
unfold consistent in *. 
intuition.
Qed.

Lemma fetch_instruction_invariant: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s}}
fetch_instruction
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
eapply weaken.
eapply fetch_instruction_wp.
intros.
simpl. 
unfold consistent in *.
case_eq (lt_dec (pc s) (length (code s))).
+ left;intuition.
+ right;intuition.
Qed.


Lemma incr_pc_invariant: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s}}
incr_pc 
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
eapply weaken. 
 + eapply incr_pc_wp.
 + intros. simpl.
   unfold consistent in *.
   intuition.
Qed.
 


Lemma interrupt_invariant n: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  }}
 interrupt n
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
eapply weaken.
eapply interrupt_wp.
simpl.
intros.
unfold consistent in *.
case_eq (lt_dec n (length (intr_table s))).
+ left;intuition.
+ right;intuition.

Qed.


Lemma return_from_interrupt_invariant : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s   }}
 return_from_interrupt
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
eapply weaken.
eapply return_from_interrupt_wp.
simpl.
intros.
unfold consistent in *;intuition.
Qed.


Lemma add_interruption_invariant (I : option nat) : 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s   }}
 add_interruption I
{{ fun index (s :state) => isolation s.(data) s.(process_list)  /\ consistent s  }}.
Proof.
eapply weaken.
eapply add_interruption_wp.
simpl.
intros.
unfold consistent in *;intuition.
Qed.


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


Lemma halt_invariant : 
{{ fun s : state => isolation (data s) (process_list s) /\ consistent s }} 
  halt {{ fun (_ : unit) (s : state) =>
          isolation (data s) (process_list s) /\ consistent s }}.
Proof.
eapply weaken.
eapply halt_wp.
tauto. 
Qed.

Lemma reset_invariant: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s}}
reset
{{ fun _  (s :state) => isolation s.(data) s.(process_list)  /\ consistent s}}.
Proof.
unfold reset.
eapply bind_wp_rev.
+ eapply create_process_invariant.
+ intros [].
  eapply bind_wp_rev.
   - eapply create_process_invariant.
   - intros []. eapply init_current_process_invariant.
Qed.
