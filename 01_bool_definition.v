(** Определяем индуктивные типы. *)

(* Пустой тип без элементов. *)

Inductive empty : Set :=
.

Check empty.

(* Тип с одним единственным элементом. *)

Inductive unit : Set :=
| item : unit
.

Check unit.
Check item.

(* Тип с двумя элементами. *)

Inductive color : Set :=
| black : color
| white : color
.

Check color.
Check black.
Check white.

Inductive bool : Set :=
| true : bool
| false : bool
.

Check bool.
Check true.
Check false.

Check Set.
Check Prop.
Check Type.

(** На множестве с двумя элементами мы можем определить функции *)

Definition eqb (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | false, false => true
    | _, _ => false
  end.

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

Definition orb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => true
| false => b2
end.

Check eqb.
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

(** Определение функции можно задать разными способами. *)

Print andb.

Definition andb1 : bool -> bool -> bool := 
fun (b1 b2 : bool) =>
(match b1 with
| true => b2
| false => false
end) : bool.


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

(* Можно доказать эквивалентность различных определений. *)

Lemma and_eq_and2 :
  forall b1 b2 : bool,
  andb b1 b2 = andb1 b1 b2.
Proof.
  intros.
  case b1, b2; reflexivity.
Qed.

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

(* Упражнение: 2 *)

Definition andb4 (b1 b2 b3 : bool) : bool :=
match (b1, b2, b3) with
| (true, true, true) => true
| (_, _, _) => false
end.

Check (true, true, true).

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

(* 
  В три банки с надписями "малиновое" "клубничное" и 
  "малиновое или клубничное" налили смородиновое, малиновое и 
  клубничное варенье. Все надписи оказались неправильными. 
  Какое варенье налили в банку с надписью "клубничное"?
*)

Inductive варенье : Set := 
| малина
| клубника
| смородина
.

Inductive банка : Set :=
| малиновое
| клубничное
| малиновое_или_клубничное
.

Definition надпись_совпадает (x : варенье * банка) : bool :=
match x with
| (малина, малиновое) => true
| (клубника, клубничное) => true
| (малина, малиновое_или_клубничное) => true
| (клубника, малиновое_или_клубничное) => true
| (_, _) => false
end.

Definition то_же_варенье (v1 v2 : варенье) : bool := 
  match v1, v2 with
    | малина, малина => true
    | клубника, клубника => true
    | смородина, смородина => true
    | _, _ => false
  end.

  Definition та_же_банка (b1 b2 : банка) : bool := 
  match b1, b2 with
    | малиновое, малиновое => true
    | клубничное, клубничное => true
    | малиновое_или_клубничное, малиновое_или_клубничное => true
    | _, _ => false
  end.

Definition повторы (x y z : варенье * банка ) : bool.
Proof.
  destruct x as [ A K ].
  destruct y as [ B L ].
  destruct z as [ C M ].
  exact (то_же_варенье A B || то_же_варенье B C || то_же_варенье A C 
      || та_же_банка K L || та_же_банка L M || та_же_банка K M ).
Defined.

Definition налили (x y z : варенье * банка ) : bool.
Proof. 
  apply(
  ^ (повторы x y z) 
  && ^ (надпись_совпадает x) 
  && ^ (надпись_совпадает y) 
  && ^ (надпись_совпадает z)).
Defined.

Compute (налили (малина, малиновое) (клубника, малиновое) (смородина, малиновое)).
Compute (налили (малина, малиновое) (клубника, клубничное) (смородина, малиновое_или_клубничное)).
Compute (налили (малина, малиновое) (клубника, малиновое_или_клубничное) (смородина, клубничное)).
Compute (налили (малина, клубничное) (клубника, малиновое) (смородина, малиновое_или_клубничное)).
Compute (налили (малина, клубничное) (клубника, малиновое_или_клубничное) (смородина, малиновое)).
Compute (налили (малина, малиновое_или_клубничное) (клубника, малиновое) (смородина, клубничное)).
Compute (налили (малина, малиновое_или_клубничное) (клубника, клубничное) (смородина, малиновое)).
