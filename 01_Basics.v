(** Определяем индуктивные типы. *)

Inductive empty : Set :=
.
Check empty.

Inductive unit : Set :=
| item : unit
.
Check unit.
Check item.

Inductive bool : Set :=
| true : bool
| false : bool
.

Check bool.
Check true.
Check false.

(** На множестве с двумя элементами мы можем определить функции *)

Definition negb (b:bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => b2
| false => false
end.

Definition orb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => true
| false => b2
end.
Check negb.
Check andb.
Check orb.

(** Функции можно вычислять *)

Compute (orb true true).    (* = true *)
Compute (orb true false).   (* = true *)
Compute (orb false true).   (* = true *)
Compute (orb false false).  (* = false *)

Compute (andb true true).    (* = true *)
Compute (andb true false).   (* = false *)
Compute (andb false true).   (* = false *)
Compute (andb false false).  (* = false *)

Compute negb (andb true (orb true false)).  (* = false *)


Lemma orb_tt :
  orb true true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma orb_tf :
  orb true false = true.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma orb_ft :
  orb false true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma orb_ff :
  orb false false = false.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma test_1 :
  negb (andb true (orb true false)) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(** Для функций можно вводить обозначения *)

Notation "^ x" := (negb x) (at level 5).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute (false || false || true).   (* = true *)

(*
(* Упражнение: 1 *)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  (* написать определение *)

Example test_nandb1 :
  (nandb true false) = true.
(* написать доказательство *)

Example test_nandb2 :
  (nandb false false) = true.
(* написать доказательство *)

Example test_nandb3 :
  (nandb false true) = true.
(* написать доказательство *) 

Example test_nandb4 :
  (nandb true true) = false.
(* написать доказательство *) 

(* Упражнение: 2 *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  (* 
  написать определение функции, 
  которая вычисляет произведение трех булевых переменных
  *)

Example test_andb31 :
  (andb3 true true true) = true.
(* написать доказательство *) 

Example test_andb32 :
  (andb3 false true true) = false.
(* написать доказательство *) 

Example test_andb33 :
  (andb3 true false true) = false.
(* написать доказательство *) 

Example test_andb34 :
  (andb3 true true false) = false.
(* написать доказательство *) 

*)

Inductive day : Set :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day
.

Definition next_weekday (d : day) : day :=
match d with
| monday    => tuesday
| tuesday   => wednesday
| wednesday => thursday
| thursday  => friday
| friday    => monday
| saturday  => monday
| sunday    => monday
end.

Compute (next_weekday friday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity.  Qed.


Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.