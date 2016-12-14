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
Require Import StateMonad.

Set Printing Projections.

Inductive result' (A : Type) : Type :=
| val : A -> result' A
| hlt : result' A
| undef : result' A.

Implicit Arguments val [ A ].
Implicit Arguments hlt [ A ].
Implicit Arguments undef [ A ].

Inductive instr : Type :=
| Nop
| Halt
| Trap (n : nat)
| Iret 
| Load  (addr : nat)
| Add_pte (permission index: nat) 
| Switch_process
| Reset
| Free (page : nat)
| Write (val Vaddr : nat)
| Exit.

Record process : Type := {
  eip : nat;
  process_kernel_mode : bool;
  cr3_save : nat;
  stack_process : list nat
}.

Record state' : Type := {
  process_list : list process;
  current_process : process;
  cr3 : nat ;
  code : list instr ;
  intr_table : list nat;
  interruptions : Stream (option nat);
  kernel_mode : bool;
  pc : nat;
  stack : list (bool * nat);
  register : nat;
  data : list nat ;
  first_free_page : nat
}.

Inductive exception : Type :=
| faultpage 
| noaccess.

Module Export HardwareMonad <: STATE_MONAD with Definition result := result' with Definition state := state'.

Definition state := state'.

Definition result := result'.

Definition M (A :Type) : Type := state -> result (A * state).

Definition ret {A : Type}(a : A) : M A :=
  fun s => val (a, s).

Definition bind {A B : Type} (m : M A)(f : A -> M B) : M B :=
  fun s => match m s with
    | val (a, s') => f a s'
    | hlt => hlt
    | undef=> undef
    end.

Notation "'perform' x ':=' m 'in' e" := (bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60, format "'[v' '[' 'perform'  x  ':='  m  'in' ']' '/' '[' e ']' ']'") : state_scope.

Notation "m1 ;; m2" := (bind m1 (fun _ => m2)) (at level 60, right associativity) : state_scope.

Open Scope state_scope.

Definition put (s : state) : M unit :=
  fun _ => val (tt, s).

Definition get : M state :=
  fun s => val (s, s).

Definition halt {A : Type} : M A :=
  fun _ => hlt.

Definition undefined {A : Type} : M A :=
  fun s => undef.

Definition run {A : Type} (m : M A) (s : state) : result (A * state) :=
  m s.

Lemma ret_left (A B : Type)(a : A)(f : A -> M B) : perform x := ret a in f x = f a.
Proof.
extensionality s; trivial.
Qed.

Lemma ret_right (A : Type)(m : M A) : perform x := m in ret x = m.
Proof.
extensionality s; unfold bind; case (m s); trivial; tauto.
Qed.

Lemma assoc (A B C : Type)(m : M A)(f : A -> M B)(g : B -> M C) :
  perform y :=
    perform x := m in
    f x in
  g y =
  perform x := m in
  perform y := f x in
  g y.
Proof.
extensionality s; unfold bind; case (m s); trivial; tauto.
Qed.

Lemma halt_left (A B : Type) (f : A -> M B) :
  perform x := halt in f x = halt.
Proof.
trivial.
Qed.

Lemma undefined_left (A B : Type) (f : A -> M B) :
  perform x := undefined in f x = undefined.
Proof.
trivial.
Qed.

Definition hoare_triple {A : Type} (P : state -> Prop) (m : M A) (Q : A -> state -> Prop) : Prop :=
  forall s, P s -> match m s with
    | val (a, s') => Q a s'
    | hlt => True
    | undef=> False
    end.

Notation "{{ P }} m {{ Q }}" := (hoare_triple P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : state_scope.

Lemma weaken (A : Type) (m : M A) (P Q : state -> Prop) (R : A -> state -> Prop) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros H1 H2 s H3.
case_eq (m s); [intros [a s'] H4 | intro H4 | intro H4 ];
apply H2 in H3; apply H1 in H3; rewrite H4 in H3; trivial.
Qed.

Definition wp {A : Type} (P : A -> state -> Prop) (m : M A) :=
  fun s => match m s with val (a, s') => P a s' | hlt => True | Err => False end.

Lemma wp_is_precondition (A : Type) (P : A -> state -> Prop) (m : M A) :
  {{ wp P m }} m {{ P }}.
Proof.
unfold wp.
congruence.
Qed.

Lemma wp_is_weakest_precondition
  (A : Type) (P : A -> state -> Prop) (Q : state -> Prop) (m : M A) :
  {{ Q }} m {{ P }} -> forall s, Q s -> (wp P m) s.
Proof.
trivial.
Qed.

Lemma post_and :
  forall (A : Type) (P : state -> Prop) (Q R : A -> state -> Prop) (m : M A),
  {{ P }} m {{ Q }} -> {{ P }} m {{ R }} -> {{ P }} m {{ fun a s => Q a s /\ R a s }}.
Proof.
intros A P Q R c H1 H2 s H3.
generalize (H1 s H3). clear H1. intro H1.
generalize (H2 s H3). clear H2. intro H2.
destruct (c s) as [ [ a s' ] | | ]; tauto.
Qed.

Lemma pre_or :
  forall (A : Type) (P Q : state -> Prop) (R : A -> state -> Prop) (m : M A),
  {{ P }} m {{ R }} -> {{ Q }} m {{ R }} -> {{ fun s => P s \/ Q s }} m {{ R }}.
Proof.
intros A P Q R c H1 H2 s H3.
destruct H3 as [H3|H3].
generalize (H1 s H3). clear H1. intro H1. assumption.
generalize (H2 s H3). clear H2. intro H2. assumption.
Qed.

Lemma ret_wp (A : Type) (a : A) (P : A -> state -> Prop) : {{ P a }} ret a {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bind_wp (A B : Type) (m : M A) (f : A -> M B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop) :
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} perform x := m in f x {{ R }}.
Proof.
intros H1 H2 s H3; unfold bind; case_eq (m s); [intros [a s'] H4 | intro H4 | intro H4];
apply H2 in H3; rewrite H4 in H3; trivial;
case_eq (f a s'); [intros [b s''] H5 | intro H5 | intro H5];
apply H1 in H3; rewrite H5 in H3; trivial.
Qed.

Lemma put_wp (s : state) (P : unit -> state -> Prop) : {{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma get_wp (P : state -> state -> Prop) : {{ fun s => P s s }} get {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma halt_wp (A : Type)(P : A -> state -> Prop) : {{ fun s => True }} halt {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma undefined_wp (A : Type)(P : A -> state -> Prop) : {{ fun s => False }} undefined {{ P }}.
Proof.
intros s H; trivial.
Qed.

End HardwareMonad.

Module Export HardwareMonadPlus := Make_StateMonadPlus (HardwareMonad).

Lemma state_eq : 
forall s s0: state , s0=s -> {| process_list := s.(process_list);
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
              data :=  s.(data) |} = s0.
Proof.
intros.
subst.
destruct s.
simpl.
reflexivity.
Qed.

(** * Parameters of the hardware *)

Definition offset_nb_bits := 4. 
Definition base_virt_page__nb_bits := 4. 
Definition base_phy_page__nb_bits := 3. 
Definition valid_bits := 1.
Definition accesPermission_bits := 1.
Definition page_size := Nat.pow 2 offset_nb_bits.
Definition phy_addr_nb_bits := base_phy_page__nb_bits + offset_nb_bits.
Definition memory_length := Nat.pow 2 phy_addr_nb_bits.
Definition virt_addr_size := base_virt_page__nb_bits + offset_nb_bits.
Definition nb_pte := Nat.pow 2 base_virt_page__nb_bits .
Definition permission_size := accesPermission_bits + valid_bits.
Definition pte_size := permission_size + base_phy_page__nb_bits.
Definition nb_page := memory_length / page_size .

Lemma nb_page_lemma : nb_page * page_size = memory_length.
Proof.
reflexivity.
Qed.
