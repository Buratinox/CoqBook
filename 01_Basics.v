(** Определяем индуктивные типы. *)

Inductive empty : Set :=
.

Check empty.

Inductive unit : Set :=
| item : unit
.

Check unit.
Check item.

Inductive color : Set :=
| black : color
| white : color
.

Check color.
Check black.
Check white.

Inductive bool : Set :=
| true 
| false
.

Check bool.
Check true.
Check false.

Check Set.
Check Type.

(** На множестве с двумя элементами мы можем определить функции *)

Definition negb (b : bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
match b1 with
| true => b2
| false => false
end.

Definition andb' := 
fun (b1 b2 : bool) =>
(match b1 with
| true => b2
| false => false
end) : bool.

Check andb'.

Check andb.
Print andb.

Definition andb2 (b1 : bool) (b2 : bool) : bool :=
match b1 with
| true => match b2 with
          | true => true
          | flse => false
          end
| false => false
end.

Definition andb3 (b1 : bool) (b2 : bool) : bool :=
match b1, b2 with
| true, true => true
| _, _ => false
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

(* Упражнение: 1 *)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  (* написать определение *)
match b1, b2 with
| true, true => false
| _, _ => true
end.

Example test_nandb1 :
  (nandb true false) = true.
(* написать доказательство *)
Proof.
  simpl.
  reflexivity.
Qed. 

Example test_nandb2 :
  nandb false false = true.
(* написать доказательство *)
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb3 :
  nandb false true = true.
(* написать доказательство *) 
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb4 :
  nandb true true = false.
(* написать доказательство *) 
Proof.
  simpl.
  reflexivity.
Qed.

Lemma and_eq_and2 :
  forall b1 b2 : bool,
  andb b1 b2 = andb2 b1 b2.
Proof.
  intros.
  case b1, b2; reflexivity.
Qed.


(* Упражнение: 2 *)

Definition andb4 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
match b1, b2, b3 with
| true, true, true => true
| _, _, _ => false
end.
Definition andb4' (b1 b2 b3 : bool) : bool := b1 && (b2 && b3).

Definition ifte (b1 b2 b3 : bool) : bool := if b1 then b2 else b3.

Definition implb (b1 b2 : bool) : bool := 
match b1 with
| true => b2
| false => true
end.

Compute ifte false true true.

Lemma andb4_eq_andb4':
  forall b1 b2 b3 : bool,
  andb4 b1 b2 b3 = andb4' b1 b2 b3.
Proof.
  intros.
  case b1, b2, b3; reflexivity.
Qed.

Example test_andb31 :
  andb4 true true true = true.
Proof.
  reflexivity. 
Qed.

Example test_andb32 :
  andb4 false true true = false.
Proof.
  reflexivity. 
Qed.

Example test_andb33 :
  andb4 true false true = false.
Proof.
  reflexivity.
Qed.

Example test_andb34 :
  andb4 true true false = false.
Proof.
  reflexivity.
Qed.

Inductive day : Set :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday
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

Compute (next_weekday monday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive Gender : Set :=
| boy : Gender
| girl : Gender
.

Inductive Student : Set :=
| ivanov : Student
| petrov : Student
| sidorova : Student
| kazakova : Student
| vladimirov : Student
.

Definition StudentGender (s : Student) : Gender := 
match s with
| ivanov => boy
| petrov => boy
| sidorova => girl
| kazakova => girl
| vladimirov => boy
end.

Compute (StudentGender sidorova).
