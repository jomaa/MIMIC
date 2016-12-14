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

(** Adddendum to Coq Standard Library  *)

Require Import Omega List Arith NPeano Omega.
Import List.ListNotations.
Require Import HMonad Coq.NArith.Ndigits  Coq.Logic.Classical_Prop. 

Definition sublist (index len : nat) (l : list nat) : list nat :=
 firstn len (skipn index l).

Definition getBase (a n:nat)  : nat :=
 a / (Nat.pow 2 n).

Definition getOffset ( a n: nat): nat :=
Nat.land a (Nat.ones n).


Definition shift_add (a b nb_bit : nat) : nat :=
  a * (Nat.pow 2 nb_bit) + b.
 
Definition removePermission (pte: nat ) : nat :=
 getBase pte permission_size.

Definition isMapped_pte (pte : nat) : bool :=
match (removePermission pte) , (getOffset pte valid_bits) with 
|0, 0 => false 
|_ , _ =>  true
end.

Definition update_sublist (index val : nat) l := 
 firstn index l ++ [val] ++ skipn (index +1) l.

Definition new_pte ( phy_page : nat) (permission : nat):  nat :=  
 shift_add (phy_page) permission permission_size .

Lemma firstn_nil : 
forall A n, firstn n nil  = @nil A.
Proof.
destruct n; trivial.
Qed.

Lemma skipn_nil : 
forall A n, skipn n nil  = @nil A.
Proof.
destruct n; trivial.
Qed. 

Lemma skipn_cons (A : Type) ( i : nat) (v : A) (l : list A) :
skipn (S i) (v :: l) =  skipn i l.
Proof.
trivial.
Qed.

Lemma skipn_length A n (l : list A) : length (skipn n l) = length l - n.
Proof.
revert l.
induction n as [ | n IH ]; intro l; simpl.
- auto with arith.
- destruct l as [ | a l ]; trivial.
  simpl; congruence.
Qed.

Lemma firstn_nth A d n len (l : list A) : n < len -> List.nth n (firstn len l) d = List.nth n l d.
Proof.
revert n len.
induction l as [ | a l IH ]; simpl; intros n len H.
- rewrite firstn_nil; trivial.
- destruct n as [ | n ]; simpl.
  + destruct len as [ | len ]; trivial; omega.
  + destruct len as [ | len ]; try omega.
    erewrite <- IH.
    * tauto.
    * omega.
Qed.

Lemma skipn_nth A d n start (l : list A) : List.nth n (skipn start l) d = List.nth (start+n) l d.
Proof.
revert n start.
induction l as [ | a l IH ]; simpl; intros n start.
- rewrite skipn_nil.
  rewrite nth_overflow; simpl; try omega.
  destruct (start + n); reflexivity.
- destruct start as [ | start ]; simpl; trivial.
Qed.

Fixpoint repeat {A : Type} (n : nat) (a : A) : list A :=
  match n with
  | O => nil
  | S n' => a :: repeat n' a
  end.

Fixpoint nth_update_by_index {A : Type}  (l : list A)  (n: nat) (b : A) {struct n} : list A :=
  match n with
  | 0 => match l with
    | [] => []
    | _ :: l' => b :: l'
    end
  | S n' => match l with
    | [] => []
    | a :: l' => a :: nth_update_by_index l' n' b
    end
  end.

Lemma nth_nth_update_by_index A d v n n' (l : list A) :
  n <> n' -> nth n l d = nth n (nth_update_by_index l n' v) d.
Proof.
revert n n'.
induction l as [ | a l IH ]; intros [ | n] [ | n'] H; trivial; simpl; try tauto.
apply IH.
congruence.
Qed.
(*
Lemma update_by_index_preserv (A : Type) (P : A -> A -> Prop)
  (len start1 start2 : nat) ( v d1 d2: A)  (n n1 n2 : nat) (l: list A) :
  n <> start1 + n1 -> n <> start2+n2 ->
  P (nth n1 (firstn len (skipn start1 l)) d1) (List.nth n2 (firstn len (skipn start2 l)) d2) ->
  P (nth n1 (firstn len (skipn start1 (nth_update_by_index l n v))) d1) (List.nth n2 (firstn len (skipn start2 (nth_update_by_index  l n v))) d2).
Proof. 
intros H1 H2 H3.
destruct (le_lt_dec len n1) as [H4 | H4].
- rewrite nth_overflow; [idtac | rewrite firstn_length; zify; omega].
  rewrite nth_overflow in H3; [idtac | rewrite firstn_length; zify; omega].
  destruct (le_lt_dec len n2) as [H5 | H5].
  + rewrite nth_overflow; [idtac | rewrite firstn_length; zify; omega].
    rewrite nth_overflow in H3; [idtac | rewrite firstn_length; zify; omega].
    exact H3.
  + rewrite firstn_nth; try tauto.
    rewrite skipn_nth.
    rewrite firstn_nth in H3; try tauto.
    rewrite skipn_nth in H3.
    rewrite <- nth_nth_update_by_index; trivial; congruence.
- destruct (le_lt_dec len n2) as [H5 | H5].
  + rewrite (@nth_overflow _ _ n2); [idtac | rewrite firstn_length; zify; omega].
    rewrite (@nth_overflow _ _ n2) in H3; [idtac | rewrite firstn_length; zify; omega].
    rewrite firstn_nth; try tauto.
    rewrite skipn_nth.
    rewrite firstn_nth in H3; try tauto.
    rewrite skipn_nth in H3.
    rewrite <- nth_nth_update_by_index; trivial; congruence.
  + rewrite firstn_nth, firstn_nth, skipn_nth, skipn_nth; try tauto.
    rewrite firstn_nth, firstn_nth, skipn_nth, skipn_nth in H3; try tauto.
    rewrite <- nth_nth_update_by_index, <- nth_nth_update_by_index; congruence.
Qed.
*)
(* FONCTION INUTILISEE *)
(** get the sublist which starts after the first occurrence of a *)
Fixpoint get_sublist_by_elemnt {A : Type} (eqb : A -> A -> bool) (l : list A) (a : A) {struct l} : list A :=
  match l with 
  |nil => nil 
  |x::l' => if eqb x a then l' else get_sublist_by_elemnt eqb l' a
  end.

(* FONCTION INUTULISEE CAR IDENTIQUE A SKIPN
Fixpoint get_sublist_by_index {A : Type} (l : list A)  (n : nat) {struct l} : list A := 
  match n, l with
  | O, a::l' => (a::l')
  | S n', _::l' => get_sublist_by_index l' n'
  | _, _ => nil 
  end.
*)

(* FONCTION INUTILISEE *)
(** replace a with b and return the position of a *)
Fixpoint nth_update_by_elemnt {A : Type} (eqb : A -> A -> bool) (l : list A) (a b: A) {struct l} : (list A * nat) :=
  match l with
  | nil => (nil, 0)
  | x :: l' => if eqb x a then (b :: l', 0) else
      let (l'', n) := nth_update_by_elemnt eqb l' a b in
      (x :: l'', S n)
  end.

(* ANCIENNE DEFINITION TROP COMPLIQUEE
Definition nth_update_by_elemnt (l : list nat) (a b: nat) : (list nat * nat) :=
let l2 := get_sublist_by_elemnt beq_nat l a in 
let n := length l - length l2 in
let l1 := firstn (n-1) l in 
((l1 ++ [b] ++ l2), n-1).
*)

Fixpoint get_index {A : Type} (beq : A -> A -> bool) (l : list A) (a : A) : nat := 
  match l with
  | [] => 0
  | b :: l' => if beq a b then 0 else S (get_index beq l' a)
  end.

Lemma length_nth_update_by_index A n v (l : list A) : length (nth_update_by_index l n v) = length l.
Proof.
revert n.
induction l as [ | a l IH ]; intros [ | n]; trivial.
simpl; congruence.
Qed.

(*

Lemma firstn_nil {A} n : firstn n (@nil A) = nil.
Proof. case n; simpl; trivial. Qed.

Lemma skipn_nil : forall {A} n (x : list A),
  length x <= n -> skipn n x = nil.
Proof.
  induction n; simpl in *; trivial; intros.
  apply length_nil; auto; omega.
  destruct x; simpl in *; trivial.
  apply IHn; omega.
Qed.*)

Lemma length_skipn : forall A n (y : list A),
  length (skipn n y) = length y - n.
Proof.
  induction n; simpl; intros; [ omega | ].
  destruct y; simpl; trivial.
Qed.
(*
Lemma skipn_length : forall {A} n (l:list A), 
  length (skipn n l) = length l - n.
Proof.
  induction n; simpl; intros; auto with arith.
  destruct l; simpl; auto.
Qed.
*)
Lemma skipn_plus :
  forall A j i (l:list A), skipn (i+j) l = skipn i (skipn j l).
Proof.
 induction j as [ | j IH]; simpl; intros.
 rewrite plus_0_r; trivial.
 rewrite <- plus_Snm_nSm.
 case l.
 rewrite !skipn_nil; simpl; trivial; omega.
 simpl; trivial.
Qed.

Lemma skipn_hd : forall {A} n y (d:A), 
  n < length y -> 
  skipn n y = List.nth n y d :: skipn (S n) y.
Proof.
 induction n; simpl; intros.
 destruct y; simpl in *; trivial.
 contradict H; omega.
 destruct y; simpl in *.
 contradict H; omega.
 apply IHn.
 omega.
Qed.

Lemma firstn_app {A} (l l' : list A) : 
  firstn (length l) (l ++ l') = l.
Proof.
 induction l; intros; simpl; trivial.
 rewrite IHl; trivial.
Qed.

Lemma skipn_app {A} (l l' : list A) : 
  skipn (length l) (l ++ l') = l'.
Proof. induction l; intros; simpl; trivial. Qed.


Lemma skipn_nil_length : forall A n (l : list A),
  skipn n l = nil -> length l <= n.
Proof.
  induction n; simpl in *; intros.
  subst; simpl; trivial.
  destruct l; simpl; [ omega | ].
  generalize (IHn _ H); omega.
Qed.


Lemma firstn_cons :
  forall A (a:A) l n, firstn (S n) (a::l) = a :: firstn n l.
Proof.
destruct n.
reflexivity.
reflexivity.
Qed.

Lemma length_firstn_le :
  forall A n (l:list A),
  (n <= length l)%nat -> length (firstn n l) = n.
Proof.
induction n as [ | n IH].
reflexivity.
intros l H.
destruct l as [ | a l].
auto with arith.
rewrite firstn_cons.
simpl.
auto with arith.
Qed.

Lemma length_skipn_le :
  forall A n (l:list A),
  (n <= length l)%nat -> length (skipn n l) = (length l - n)%nat.
Proof.
induction n as [ | n IH].
auto with arith.
intros l H.
destruct l as [ | a l].
reflexivity.
rewrite skipn_cons.
simpl.
apply IH.
auto with arith.
Qed.

Lemma skipn_app_le (A : Type):
forall l1 l2 : list A , forall n,  
n <= length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.  
induction l1;intros;simpl.
 + simpl in H. case_eq n;intros.
   - simpl. reflexivity.
   - subst. omega.
 + case_eq n;intros.
   - simpl. reflexivity.
   - subst. simpl. apply IHl1.  auto with *.
Qed.

Lemma skipn_app_lt (A : Type):
 forall l1 l2 : list A , forall n, 
  length l1 <= n -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof.
induction l1;intros;simpl.
 + simpl in H. case_eq n;intros.
   - simpl. reflexivity.
   - subst. trivial. 
 + case_eq n;intros.
   - simpl. subst. simpl in H. contradict H. intuition.
   - subst. simpl. apply IHl1.  auto with *.
Qed. 

Lemma firstn_gt_length (A : Type) : 
forall l : list A,  forall n ,  length l <= n ->  firstn n l = l.
Proof.
induction l; simpl.
 + intros. apply firstn_nil.
 + intros. destruct n.
   - simpl. auto with *.
   - simpl.  rewrite IHl. 
     * reflexivity.
     * auto with *.
Qed.


Lemma skipn_firstn (A : Type) : 
forall l: list A , forall i j ,
  i <= j -> skipn i (firstn j l) = firstn (j - i) (skipn i l).
Proof.
induction l;simpl;intros.
 + rewrite skipn_nil. rewrite ?firstn_nil. rewrite skipn_nil.  trivial.
 + case_eq i.
   - simpl. intros. auto with *. simpl. subst.
     rewrite <- minus_n_O. reflexivity.
   - intros. subst. case_eq j.
     * simpl. trivial.
     * intros. subst.  simpl. apply IHl.  auto with *. 
Qed.

Lemma firstn_skipn (A : Type) (l: list A ) i j :
  firstn i (skipn j l) = skipn j (firstn (i + j) l).
Proof. 
rewrite skipn_firstn.
rewrite Nat.add_sub. 
reflexivity.
auto with *.
Qed.

Lemma sublist_skipn : 
forall len l, skipn len l = sublist len (length l) l.
Proof. 
intros.
unfold  sublist. 
rewrite  firstn_skipn. 
rewrite firstn_gt_length.
reflexivity.
omega.
Qed.
 



Lemma firstn_firstn (A: Type):
 forall l:list A, forall i j : nat,  
  firstn i (firstn j l) = firstn (min i j) l.
Proof.
 induction l as [|x xs Hl].
    - intros. simpl.  repeat rewrite firstn_nil. reflexivity.
    - destruct i.
      * intro. now simpl.
      * destruct j.
        + simpl. reflexivity.
        + simpl. f_equal. apply Hl.
Qed.

Lemma sublist_firstn : 
forall len l, firstn len l = sublist O len l.
Proof. 
intros.
now simpl.
Qed.





Lemma firstn_app_le (A :Type): 
forall l1 l2 : list A , forall i, 
i <= length l1 -> firstn i (l1 ++ l2) = firstn i l1.
Proof.
 induction l1; simpl.
 + intros. destruct i. simpl. reflexivity.  contradict H.  auto with *.
 + intros. destruct i.
   - simpl. auto with *.
   - simpl.  rewrite IHl1. 
     * reflexivity.
     * auto with *.
Qed.

Lemma sublist_app_le : 
forall l1 l2 len i,  i + len <= length l1  -> 
 sublist i len (l1 ++ l2) =   sublist i len l1.
Proof. 
intros.
unfold sublist. rewrite firstn_skipn. rewrite firstn_skipn.
 apply f_equal.
apply firstn_app_le. auto with *. 
Qed.

Lemma sublist_zero_app_eq : 
forall l1 l2 len,  len = length l1  -> 
 sublist 0 len (l1 ++ l2) = l1.
Proof. 
intros.
unfold sublist. rewrite firstn_skipn. 
rewrite firstn_app_le.
rewrite skipn_firstn.
simpl.
rewrite Nat.add_sub.
rewrite firstn_gt_length with nat l1 len.
reflexivity.  
auto with *.
auto with *.
auto with *. 
Qed.



Lemma and_gt_plus : 
forall i j ,  (S i  > j /\ S j  > i) ->  j = i.
Proof. 
intros.
destruct H.
apply gt_S_le in H.
destruct H.
trivial. 
apply Nat.le_le_succ_r in H. 
apply Nat.le_succ_r in H.
destruct H. apply gt_S_n in H0. 
contradict H0. intuition. assumption.  
Qed.

Lemma skipn_skipn(A: Type): forall n m (l: list A),
skipn n (skipn m l) = skipn (m + n) l.
Proof.
intros.
revert l; induction m; intros.
+ reflexivity.
+ simpl.
destruct l.
- destruct n; reflexivity.
- apply IHm.
Qed.

Lemma repeat_length (A: Type): forall n, forall x: A, length (repeat n x) = n.
Proof.
induction n; intros. reflexivity. simpl. rewrite IHn. reflexivity.
Qed.

Lemma sublist_two_app : 
forall l1 l2 l3, forall i len, length (l1 ++ l2 ) <= i -> 
 sublist i len (l1 ++ l2 ++ l3) = sublist (i - (length l1 + length l2))   len l3.
Proof.
intros. 
unfold sublist.
rewrite app_assoc.
set (l4 := l1 ++ l2).
rewrite skipn_app_lt .
unfold l4.
rewrite app_length.
reflexivity.
unfold l4. assumption. 
Qed.

Lemma sublist_eq_two_app : 
forall l1 l2 l3, forall i len, length l1 = i -> 
 sublist i len (l1 ++ l2 ++ l3) = sublist 0 len (l2 ++ l3).
Proof.
intros.
unfold sublist.

set (l4 := l2 ++ l3).
simpl. 
symmetry in H.
rewrite H. 
rewrite skipn_app. reflexivity. 
Qed.


Lemma insert_sublist_unchanged  a :   
forall i j l, length l > i+1-> length l > j+1 -> 
( i + 1 <= j  \/ j + 1 <= i ) -> 
sublist i 1 l = sublist i 1  (firstn j l ++ [a] ++ skipn (j + 1) l).
Proof.
intros.
destruct H1. 

 + set (l2 := [a] ++ skipn (j + 1) l).  rewrite sublist_firstn. rewrite sublist_app_le.
   - unfold sublist. rewrite firstn_skipn. rewrite firstn_skipn.
     rewrite firstn_firstn. rewrite Min.min_l.  reflexivity. auto with *.  
   - simpl. 
     unfold sublist. 
     simpl. rewrite firstn_length.
     simpl. rewrite Min.min_l. assumption. auto with *.
 + rewrite sublist_two_app.
   - unfold sublist.
     rewrite skipn_skipn.
     rewrite firstn_length. Opaque firstn skipn.
     simpl.
     rewrite Min.min_l.
      * rewrite Nat.add_sub_assoc.
        set (b := j+1). rewrite minus_plus. reflexivity.
        assumption.
      * auto with *.
   - rewrite app_length.  
     rewrite firstn_length. simpl.
     rewrite Min.min_l. auto with *. auto with *. 

Qed. 

Lemma sublist_length (index len : nat) (l : list nat) :
index + len <= length l -> length (sublist index len l) = len.
 Proof.
unfold sublist. 
rewrite firstn_skipn. 
intros.
rewrite skipn_length.
rewrite firstn_length.
rewrite min_l;omega.
Qed.

Lemma sublist_ident :
forall l len, length l = len -> sublist 0 len l = l. 
Proof. 
intros. 
unfold sublist. 
simpl.
apply firstn_gt_length.
intuition. 
Qed. 
Lemma in_insert_app (A : Type): 
forall l1 l2 : list A , forall a b c, In a ((l1 ++ [b]) ++ l2) -> a = b \/ (In a (l1 ++ [c] ++ l2)).
Proof. 
intros.
 set (l := (l1 ++ [b])) in H.
 apply in_app_or in H.
 destruct H.
 + unfold l in *.
   apply in_app_or in H.
   destruct H.
    - right.
      set ( l3 := [c] ++ l2). 
         apply in_or_app.
         left. assumption. 
     - left. simpl in H. intuition.  
 + right. 
    set ( l3 := [c] ++ l2). 
         apply in_or_app.
         right. unfold l3. simpl.  right. assumption. 
Qed.


Lemma skipn_get_index l a index :
  index = get_index beq_nat l a ->
  index < length l ->
  skipn index l = [a] ++ skipn (S index) l.
Proof.
Transparent firstn skipn.
revert index.
induction l as [ | b l IH ]; simpl; intro index.
- intros. simpl.  omega.
- intros H1 H2. simpl. 
  destruct index as [ | index ].
  + simpl.
    case_eq (beq_nat a b).
    * intro. apply beq_nat_true in H.
      congruence. 
    * intro. contradict H1.
      case_eq (beq_nat a b) .
      intros. contradict H. congruence.  
      intuition.
  + simpl (skipn (S index) (b :: l)).
    apply IH; try omega.
    destruct (beq_nat a b); congruence.
Qed.


Lemma not_eq_and_le_lt :
forall a b c, b <> a -> c > 0->
a * c < b * c \/
b * c + c <= a * c.
Proof. 
intros.  
apply not_eq_sym in H.  apply not_eq in H.
destruct H.
 + left. apply Nat.mul_lt_mono_pos_r. omega. assumption.
 + right.  auto with *.
   replace (b  * c + c) with (S b * c).
    - apply Nat.mul_le_mono_pos_r .
      omega.
      apply gt_le_S. assumption.
    - apply mult_succ_l. 
Qed. 

Lemma skipn_cons' : forall T n a (b : list T),
  0 < n ->
  skipn n (a :: b) = skipn (n - 1) b.
Proof.
  destruct n; intros.
  omega.
  simpl.
  cutrewrite (n - 0 = n); [ | omega ].
  reflexivity.
Qed.

Lemma In_skipn  (x : nat) l:        
forall i  , In x (skipn (i+1) l) -> In x (skipn i l).
Proof.
induction l.
+ intros. rewrite skipn_nil in *.  assumption. 
+ intros.
 case_eq i.
 intros.
 subst.
 - simpl in *. right.  assumption.
 - intros. 
   rewrite <- H0 in *.
   generalize (IHl (i -1) ).
   intros.   
   rewrite Nat.add_1_r in H.
   rewrite skipn_cons in H. 
   intros. 
   rewrite Nat.sub_add in H1.
   apply H1 in H.
   rewrite skipn_cons'.
   assumption.
   intuition.
   intuition. 
Qed. 

Lemma filter_app : 
forall (A : Type) (f : A -> bool) (l1 l2 : list A),
filter f l1 ++ filter f l2 =
filter f (l1 ++ l2).
Proof.
intros.
induction l1. simpl. reflexivity.
simpl.
case_eq(f a ).
intros. simpl.
f_equal. assumption.
intros.
assumption.
Qed.

Lemma In_notIn (A: Type) : 
forall a b : A, forall l, In a l -> ~ In b l -> b <> a.
Proof.
intros.
unfold not  in *. 
intros. 
apply H0. 
subst.
assumption.
Qed.


Lemma remove_add_permission page permission:
permission < 4 ->
removePermission (new_pte page permission) = page.
Proof.  
unfold removePermission. 
unfold new_pte.
unfold shift_add. 
unfold permission_size.
simpl. 
unfold valid_bits.
unfold getBase.
simpl (2 ^ 2).
rewrite Nat.div_add_l;intuition.
rewrite Nat.div_small.
intuition.
assumption.
Qed.

Lemma permission_bound :
forall b, getOffset b permission_size < 2 ^permission_size. 
Proof.
intros.
unfold getOffset.
rewrite Nat.land_ones.
unfold permission_size.
simpl (2 ^ (accesPermission_bits + valid_bits)).
apply Nat.mod_upper_bound. intuition.
Qed.

Lemma add_remove_permission : 
forall b ,
b = new_pte (removePermission b) (getOffset b permission_size).
Proof. 
unfold new_pte. 
unfold removePermission.
intros.
unfold getOffset.
rewrite Nat.land_ones.
unfold shift_add.
unfold getBase.
simpl(2 ^ permission_size).
replace (b / 4 * 4 ) with (4 * (b / 4)).
rewrite <- Nat.div_mod with b 4.
reflexivity.
omega. 
intuition.
Qed.

Lemma list_app_l (A: Type) : 
forall l1 l2 l3 : list A,  l2 = l3 -> l1++l2 = l1++l3.
Proof.
intros.
rewrite H.
reflexivity.
Qed.
Lemma NoDup_app A (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~In x l2) ->
  NoDup (l1 ++ l2).
Proof.
intro H1.
revert l2.
induction H1 as [ | x l1 H4 H5 IH ]; intros l2 H2 H3; trivial.
simpl.
constructor.

- assert (~In x l2) as H6.
  { auto with *. }
  rewrite in_app_iff.
  tauto.

- apply IH; trivial.
  auto with *.
Qed.

Lemma NoDup_split (A: Type) :
forall l l': list A , 
NoDup (l++l') -> NoDup l /\ NoDup l'.
Proof. 
intros.
split. 
 + induction l'. 
   rewrite app_nil_r in H.
   assumption.
   apply IHl'.
   apply NoDup_remove_1 in H.
   assumption.
 + induction l'. 
   apply NoDup_nil.
   assert (NoDup (l ++ a :: l')). assumption.
   apply NoDup_remove_2 in H.
   constructor 2.
   unfold not in *. intro. apply H.
   apply in_or_app.
   right. assumption.
   apply IHl'.
   apply NoDup_remove_1 in H0.
   assumption.
Qed.

Lemma NoDup_add_app (A: Type) :
forall l l': list A , forall  x, ~ In x l -> ~ In x l' -> NoDup(l++l') ->  NoDup(l++ x::l').
Proof.
intros.
apply NoDup_app.
  + induction l'.
    rewrite app_nil_r in H1. assumption.
    apply IHl'.
    unfold not in *.
    intro.
    apply H0.
    apply in_cons.
    assumption.
    apply NoDup_remove_1 with a.
    assumption.
  + constructor 2.
    assumption.
    apply NoDup_split in H1.
    intuition.
  + intros.
    simpl.
    apply and_not_or.
    split.
    - subst. 
      intuition. subst.
      intuition.
    - clear H H0. 
      induction l'.
      intuition.
      unfold not in *. 
      intros.
      assert ( NoDup (l ++ a :: l')). assumption.
      apply NoDup_remove_2 in H1.
      contradict H1.
      apply in_or_app.
      simpl in H.
      destruct H. 
      subst. intuition. 
      apply NoDup_remove_1 in H0.
      apply IHl' in H0. 
      contradiction. assumption. 
Qed.


             
Lemma le_lt_plus : 
forall a b c q, b < q -> a + q <= c -> a+b < c. 
Proof. 
intros.

apply  le_lt_or_eq in H0. 
destruct H0.
rewrite <- H0.
apply plus_lt_compat_l. 
assumption. 
rewrite <- H0.
 apply plus_lt_compat_l. 
assumption. 
Qed.
Lemma tl_In (A : Type):
forall x : A , forall l,  In x (List.tl l) -> In x l.
Proof.
intros. 
induction l.
 + simpl in *. assumption.
 + simpl in *. right. assumption.
Qed.
  
      
Lemma nth_in_sublist l: 
forall start idx len d, 
 start + len <= length l -> idx < len -> In (List.nth (start+idx) l d) (sublist start len l). (* \/ List.nth idx (firstn len (skipn start l)) d = d. *)
Proof.
intros.
rewrite <- skipn_nth.
unfold sublist.
set (l1:=(skipn start l) ).
rewrite <- firstn_nth with nat d idx len l1.
+ set(l2:=  (firstn len l1)).
  apply nth_In.
  unfold l2.
  unfold l1.
  replace (firstn len (skipn start l)) with (sublist start len l).
  rewrite sublist_length.
  assumption.
  assumption.
  unfold sublist.
  trivial. 
+ assumption. 
Qed.
  