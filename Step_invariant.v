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
Require Import Lib HMonad MMU Step Properties LibOs Scheduler_invariant Instructions_invariants Addpte_invariant Write_invariant
Removepte_invariant.

Lemma step_invariant: 
{{ fun s :state => isolation s.(data) s.(process_list)  /\ consistent s  }}
step
{{ fun _  (s :state) =>  isolation s.(data) s.(process_list)  /\ consistent s }}.
Proof.
unfold step.
eapply bind_wp_rev.
eapply fetch_interruption_invariant.
intros a. 
destruct a.
eapply interrupt_invariant.
eapply bind_wp_rev.
eapply fetch_instruction_invariant.
intros inst.
destruct inst.
 + eapply incr_pc_invariant.
 + eapply halt_invariant.
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros [].
   eapply interrupt_invariant.
 + eapply return_from_interrupt_invariant.
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros [].
   eapply load_invariant.
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros [].
   eapply add_pte_invariant. 
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros [].
   eapply switch_process_invariant.
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros []. 
   eapply reset_invariant.
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros []. 
   eapply remove_pte_invariant.
 + eapply bind_wp_rev. 
   eapply incr_pc_invariant. intros [].
   eapply write_invariant.
 + eapply weaken. eapply ret_wp.
   trivial.
Qed.