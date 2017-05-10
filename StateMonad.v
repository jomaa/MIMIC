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

(** The state monad *)

(** * The signature of a state monad module *)
Require Import List.
Module Type STATE_MONAD.

Parameter state : Type.

Parameter result : Type -> Type.

Parameter M : Type -> Type.

Parameter ret : forall {A : Type}, A -> M A.

Parameter bind : forall {A B : Type}, M A -> (A -> M B) -> M B.

Notation "'perform' x ':=' m 'in' e" := (bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60, format "'[v' '[' 'perform'  x  ':='  m  'in' ']' '/' '[' e ']' ']'") : state_scope.

Notation "m1 ;; m2" := (bind m1 (fun _ => m2)) (at level 60, right associativity) : state_scope.

Open Scope state_scope.

Parameter put : state -> M unit.

Parameter get : M state.

Parameter halt : forall {A : Type}, M A.

Parameter undefined : forall {A : Type}, M A.

Parameter run : forall {A : Type}, M A -> state -> result (A * state).

Axiom ret_left : forall (A B : Type)(a : A)(f : A -> M B), perform x := ret a in f x = f a.

Axiom ret_right : forall (A : Type)(m : M A), perform x := m in ret x = m.

Axiom assoc : forall (A B C : Type)(m : M A)(f : A -> M B)(g : B -> M C), 
  perform y :=
    perform x := m in
    f x in
  g y =
  perform x := m in
  perform y := f x in
  g y.

Axiom halt_left : forall (A B : Type) (f : A -> M B), perform x := halt in f x = halt.

Axiom undefined_left : forall (A B : Type) (f : A -> M B), perform x := undefined in f x = undefined.

Parameter hoare_triple : forall {A : Type}, (state -> Prop) -> M A -> (A -> state -> Prop) -> Prop.

Notation "{{ P }} m {{ Q }}" := (hoare_triple P m Q)
  (at level 90, format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'") : state_scope.

Axiom weaken : forall (A : Type) (m : M A) (P Q : state -> Prop) (R : A -> state -> Prop),
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.

Parameter wp : forall {A : Type}, (A -> state -> Prop) -> M A -> state -> Prop.

Axiom wp_is_precondition : forall (A : Type) (P : A -> state -> Prop) (m : M A),
  {{ wp P m }} m {{ P }}.

Axiom wp_is_weakest_precondition :
  forall (A : Type) (P : A -> state -> Prop) (Q : state -> Prop) (m : M A),
  {{ Q }} m {{ P }} -> forall s, Q s -> (wp P m) s.

Axiom post_and : forall (A : Type) (P : state -> Prop) (Q R : A -> state -> Prop) (c : M A),
  {{ P }} c {{ Q }} -> {{ P }} c {{ R }} -> {{ P }} c {{ fun a s => Q a s /\ R a s }}.

Axiom pre_or :
  forall (A : Type) (P Q : state -> Prop) (R : A -> state -> Prop) (m : M A),
  {{ P }} m {{ R }} -> {{ Q }} m {{ R }} -> {{ fun s => P s \/ Q s }} m {{ R }}.

Axiom ret_wp : forall (A : Type) (a : A) (P : A -> state -> Prop), {{ P a }} ret a {{ P }}.

Axiom bind_wp :
  forall (A B : Type) (m : M A) (f : A -> M B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop),
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} perform x := m in f x {{ R }}.

Axiom put_wp : forall (s : state) (P : unit -> state -> Prop), {{ fun _ => P tt s }} put s {{ P }}.

Axiom get_wp : forall (P : state -> state -> Prop), {{ fun s => P s s }} get {{ P }}.

Axiom halt_wp : forall (A : Type)(P : A -> state -> Prop), {{ fun s => True }} halt {{ P }}.

Axiom undefined_wp : forall (A : Type)(P : A -> state -> Prop), {{ fun s => False }}undefined {{ P }}.

End STATE_MONAD.

(** * Generic function and lemmas for state monad *)

Module Make_StateMonadPlus (M : STATE_MONAD).


Import M.

Lemma bind_wp_rev (A B : Type) (m : M A) (f : A -> M B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perform x := m in f x {{ R }}.
Proof.
intros; eapply bind_wp; eassumption.
Qed.

Lemma get_wp_eq :
forall P : state -> state -> Prop, {{ fun s : state => P s s }} get {{ fun s1 s2 => P s1 s2 /\ s1 = s2 }}.
Proof.
intro P.
eapply weaken.
- apply get_wp.
- simpl; tauto.
Qed.

Definition map {A B : Type} (f : A -> B) (m : M A) : M B :=
  perform x := m in
  ret (f x).

Lemma map_wp (A B : Type) (f : A -> B) (m : M A) (P : state -> Prop) (Q : B -> state -> Prop) :
  {{ P }} m {{ fun a s => Q (f a) s }} -> {{ P }} map f m {{ Q }}.
Proof.
intro H; eapply bind_wp.
intro a; eapply weaken.
apply ret_wp.
instantiate (1 := fun a s => Q (f a) s); trivial.
exact H.
Qed.

Definition join {A : Type} (m : M (M A)) : M A :=
  perform x := m in
  x.

Lemma join_wp (A : Type) (m : M (M A)) (P : state -> Prop) (Q : M A -> state -> Prop) (R : A -> state -> Prop) :
  (forall m', {{ Q m' }} m' {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} join m {{ R }}.
Proof.
intros; apply bind_wp with Q; assumption.
Qed.

Fixpoint hd {A : Type} (l : list A) : M A :=
  match l with
  | nil => undefined
  | h :: _ => ret h
  end.

Lemma hd_wp (A : Type) (P : A -> state -> Prop) (l : list A) : {{ fun s => exists x l', l = x::l' /\ P x s }} hd l {{ P }}.
Proof.
destruct l as [ | x l]; simpl; eapply weaken.
apply undefined_wp.
simpl.
intros s (x & l & H & _); discriminate H.
apply ret_wp.
intros s (x4 & l4 & H1 & H2); injection H1; intros; subst; trivial.
Qed.

Fixpoint tl {A : Type} (l : list A) : M (list A) :=
  match l with
  | nil => undefined
  | _ :: t => ret t
  end.

Lemma tl_wp (A : Type) (P : list A -> state -> Prop) (l : list A) : {{ fun s => exists x l', l = x::l' /\ P l' s }} tl l {{ P }}.
Proof.
destruct l as [ | x l]; simpl; eapply weaken.
apply undefined_wp.
simpl; intros s (x & l & H & _); discriminate H.
apply ret_wp.
intros s (x4 & l4 & H1 & H2); injection H1; intros; subst; trivial.
Qed.

Fixpoint nth {A : Type}(n : nat)(l : list A) {struct l} : M A :=
  match n, l with
  | O, a::_ => ret a
  | S n', _::l' => nth n' l'
  | _, _ => undefined
  end.

Lemma nth_wp (A : Type) (n : nat) (l : list A) (P : A -> state -> Prop) :
  {{ fun s => n < length l /\ forall d, P (List.nth n l d) s }} nth n l {{ P }}.
Proof.
revert l.
induction n as [ | n IH]; intros [ | a l]; simpl.
eapply weaken.
apply undefined_wp.
simpl; intros s [H _]; inversion H.
eapply weaken.
apply ret_wp.
tauto.
eapply weaken.
apply undefined_wp.
simpl; intros s [H _]; inversion H.
eapply weaken.
apply IH.
firstorder.
Qed.

Definition try {A : Type}(a : option A) : M A :=
  match a with
  | None => undefined
  | Some a0 => ret a0
  end.

Lemma try_wp (A : Type) (a : option A) (P : A -> state -> Prop) :
  {{ fun s => exists a0, a = Some a0 /\ P a0 s }} try a {{ P }}.
Proof.
destruct a as [ | a0]; simpl.
eapply weaken.
apply ret_wp.
intros s [a0 [H1 H2] ]; congruence.
eapply weaken.
apply undefined_wp.
intros s [a0 [H _] ]; discriminate H.
Qed.

Definition modify (f : state -> state) : M unit :=
  perform s := get in put (f s).

Lemma modify_wp (f : state -> state) (P : unit -> state -> Prop) :
{{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
eapply bind_wp_rev.
- eapply weaken.
  + apply get_wp.
  + simpl.
    instantiate (1 := fun s _ => P tt (f s)).
    trivial.
- intro s.
  simpl.
  apply put_wp.
Qed.

End Make_StateMonadPlus.

