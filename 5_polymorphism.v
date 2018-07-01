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
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Definition swap {X Y : Type} (p : X * Y) : Y * X :=
  match p with
  | (x, y) => (y,x)
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

Inductive list (X:Type) : Type :=
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

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(** To use [repeat] to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

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

Fixpoint rev {X:Type} (l:list X) : list X.
Admitted.

Fixpoint length {X : Type} (l : list X) : nat.
Admitted.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. Admitted.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. Admitted.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. Admitted.

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
Proof. Admitted. 

Theorem app_assoc : 
  forall X (l m n : list X),
  l ++ m ++ n = (l ++ m) ++ n.
Proof. Admitted.

Lemma app_length :
  forall (X : Type)(l1 l2 : list X),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof. Admitted.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof. Admitted.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* какой тип у этой функции? чему равно значение
Compute (combine [1;2] [false;false;true;true]).
*)

(* обратная фнукция к [combine] *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* написать фнкцию *). Admitted.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. Admitted.

