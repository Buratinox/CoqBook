Set Warnings "-notation-overridden,-parsing".
Require Export List.
(** * Полиморфизм *)

(* ================================================================= *)
(** ** Пары *)

Module pairs.

(* Для каждого базового типа определяем тип рары *)

Inductive bool : Set :=
| true : bool
| false : bool
.
Inductive boolprod : Set :=
| boolpair : bool -> bool -> boolprod
.

Inductive day : Set :=
| monday
| tuesday
| wendnsday
| thursday
| friday
| saturday
| sunday
.
Inductive dayprod : Set :=
| daypair : day -> day -> dayprod.

Inductive nat : Set :=
| O : nat
| S : nat -> nat
.
Inductive natprod : Set :=
| natpair : nat -> nat -> natprod.

(* Можно дать общее определение *)

Inductive prodset (X Y : Set) : Set :=
| pairset : X -> Y -> prodset X Y
.

Inductive prodtype' (X Y : Type) : Type :=
| pairtype' : X -> Y -> prodtype' X Y
.

Compute (pairtype' bool nat true O).

Check prodtype'.
Check pairtype' bool bool.
Check pairtype'.

Compute (pairtype' _ _ true O).

Compute (pairtype' _ _ monday (pairtype' _ _ false 4)).

Arguments pairtype' {X} {Y} _ _.

Compute (pairtype' true O).

Inductive prod {X Y : Type} : Type :=
| pair : X -> Y -> prod
.
Compute (pair true O).

End pairs.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y).

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Definition swap {X Y : Type} (p : X * Y) : Y * X :=
  match p with
  | (x, y) => (y, x)
  end.

Compute (swap (true, 13)).

Inductive day : Set :=
| monday
| tuesday
| wendnsday
| thursday
| friday
| saturday
| sunday
.
Compute (monday, (false, 4)).

(** ** Списки *)

Reset Initial.

Inductive boollist : Type :=
  | boolnil : boollist
  | boolcons : bool -> boollist -> boollist.

  Inductive natlist : Type :=
  | natnil : natlist
  | natcons : nat -> natlist -> natlist.

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check list.
(* ===> list : Type -> Type *)

Check (nil nat).
(* ===> nil nat : list nat *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

Check nil.
(* ===> nil : forall X : Type, list X *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Compute (repeat nat 4 2).

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(** To use [repeat] to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Compute (repeat bool false 4).

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' X x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.


Compute (cons 1 (cons 2 (cons 3 nil))).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(*  механизм неявных типов обычно не используется при 
    определении самих индуктивных типов *)

Inductive list' {X : Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

  Fixpoint app' {X : Type} (l1 l2 : @list' X) : list' :=
  match l1 with
  | nil'      => l2
  | cons' h t => cons' h (app' t l2)
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

  Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
                     Notation "[ ]" := nil.

                     Notation "n :: l" := (cons  n l)
                                          (at level 60, right associativity).
                     Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
                     
Fixpoint rev {X : Type} (l : list X) : list X :=
match l with 
| nil => nil
| h :: t => (rev t) ++ [h]
end.

Fixpoint length {X : Type} (l : list X) : nat :=
match l with
| [] => O
| n :: l' => S (length l')
end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. 
  reflexivity.
Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. 
  reflexivity.
Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. 
  reflexivity.
Qed.

Notation "x :: y" := (cons x y)
 (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Compute ([1; 2; 3]).
Compute ([true; false; false]).

Definition list123_ := [1; 2; 3].

Theorem app_nill_r :
  forall (X : Type) (l : list X),
  l ++ [] = l.
Proof. 
  intros*.
  induction l; simpl. reflexivity.
  rewrite IHl. reflexivity.
Qed. 

Theorem app_assoc : 
  forall X (l m n : list X),
  l ++ m ++ n = (l ++ m) ++ n.
Proof. 
  intros*.
  induction l; simpl. reflexivity.
  rewrite IHl. reflexivity.
Qed.

Lemma app_length :
  forall (X : Type)(l1 l2 : list X),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros*.
  induction l1; simpl. reflexivity.
  rewrite IHl1. reflexivity.
Qed.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. 
  intros*.
  induction l1; simpl.
  -rewrite app_nill_r. reflexivity.
  -rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof. 
  intros*.
  induction l; simpl. reflexivity.
  rewrite rev_app_distr. rewrite IHl. reflexivity.
Qed.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.
(*  ==> forall X Y : Type, list X -> list Y -> list (X * Y)
*)
(* какой тип у этой функции? чему равно значение *)
Compute (combine [1;2] [false;false;true;true]).
(* ==> [(1, false); (2, false)] *)

(* обратная фнукция к [combine] *)

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
match l with
| [] => ([], [])
| (f, s) :: t => ((f :: fst (split t)), (s :: snd (split t)))
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. 
  reflexivity.
Qed.

Theorem app_eq_nil : 
  forall (A : Type) (l l' : list A), 
  l ++ l' = [] -> l = [] /\ l' = [].
Proof. 
  destruct l as [| x l]; destruct l' as [| y l']; simpl; auto.
  intro; discriminate.
  intros H. discriminate H.
Qed.

Theorem app_comm_cons : 
forall A : Type,
  forall (x y:list A) (a:A), 
  a :: (x ++ y) = (a :: x) ++ y.
Proof. 
  intros*.
  induction x; simpl; reflexivity.
Qed.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
match n with
|O => nil
|S n' => match l with
      |nil => nil
      |h :: t => h :: take n' t
      end
end.
      
Fixpoint skip {A : Type} (n : nat) (l : list A) : list A :=
match n with
|O => l
|S n' => match l with
      |nil => nil
      |h :: t => skip n' t
      end
end.

Compute (take 5 [1;2;3;4;5;6;7]).
Compute (skip 5 [1;2;3;4;5;6;7]).

Lemma firstn_skipn : 
  forall (A : Type) (n : nat) (l : list A), 
  take n l ++ skip n l = l.
Proof.
  intros*.
  induction n. simpl. reflexivity.
  rewrite <- IHn. 

Qed.