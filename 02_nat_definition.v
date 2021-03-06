
(** ** Определение натуральных чисел *)

Module NatNumbers.

Inductive nat : Set :=
| O : nat
| S : nat -> nat
.

Check nat.
Check O.
Check S.
Check (S O).
Check (S (S O)).

Definition pred (n : nat) : nat :=
match n with
| O => O
| S m => m
end.

Compute pred (S (S (S (S O)))).
  (* = S (S (S O))
     : nat *)
Compute pred O.


End NatNumbers.

Compute (S (S (S (S O)))).
Compute pred (S (S (S (S O)))).
  (* = 4 
     : nat *)

Check pred (S (S (S (S O)))).
  (* ===> 4 : nat *)

Print NatNumbers.pred.

Definition minustwo (n : nat) : nat :=
match n with
| O => O
| S O => O
| S (S m) => m
end.

Check minustwo.

Compute (minustwo 5).
  (* ===> 2 : nat *)


Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
match n with
| O        	=> true
| S O      	=> false
| S (S m) 	=> evenb m
end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1 : 
  oddb 1 = true.
Proof. 
  reflexivity.
Qed.
Example test_oddb2 :
  oddb 4 = false.
Proof.
  reflexivity.
Qed.

Module NatNumbers2.

Fixpoint plus n m :=
match n with
| O => m
| S k => S (plus k m)
end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S k => plus m (mult k m)
end.

Example test_mult1 : 
  (mult 3 3) = 9.
Proof.
  reflexivity.
Qed.

Fixpoint minus (n m : nat) : nat :=
match n, m with
| O   , _    => O
| S _ , O    => n
| S n', S m' => minus n' m'
end.

End NatNumbers2.

Fixpoint exp (n m : nat) : nat :=
match m with
| O => S O
| S p => mult n (exp n p)
end.


Fixpoint factorial (n : nat) : nat :=
  (* написать определени факторила *)
match n with
| O => S O
| S p => mult n (factorial p)
end.



Example test_factorial1 :
  (factorial 3) = (plus 2 4).
Proof. 
  reflexivity. 
Qed.

Example test_factorial2 :
  (factorial 5) = (mult 10 12).
Proof. 
  reflexivity. 
Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Compute (2 + 3 * 4).

Check ((0 + 1) + 1).


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O 	  => 	match m with
				      | O => true
         		  | S m' => false
         		  end
  | S n'	=>	match m with
            	| O => false
            	| S m' => beq_nat n' m'
            	end
  end.

Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>	match m with
     		  | O => false
      		| S m' => leb n' m'
      	  end
end.

Example test_leb1 :
  (leb 2 2) = true.
Proof.
  simpl.
  reflexivity.  
Qed.
Example test_leb2 :
  (leb 2 4) = true.
Proof. 
  simpl.
  reflexivity.
Qed.
Example test_leb3 :
  (leb 4 2) = false.
Proof.
  simpl.
  reflexivity.  
Qed.

(*

Definition blt_nat (n m : nat) : bool :=
  (* написать фуекцию не используя рекурсию *)

Example test_blt_nat1 :
  (blt_nat 2 2) = false.
  (* проверить функцию *)

Example test_blt_nat2 :
  (blt_nat 2 4) = true.
  (* проверить функцию *)

Example test_blt_nat3 :
  (blt_nat 4 2) = false.
  (* проверить функцию *)
*)

(* ################################################################# *)
(** Доказательство простых теорем о натуральных числах *)

Theorem plus_O_n : 
  forall n : nat, 
  0 + n = n.
Proof.
  intros n. 
  simpl. 
  reflexivity.  
Qed.

Theorem plus_1_l : 
  forall n : nat, 
  1 + n = S n.
Proof.
  intros n. 
  reflexivity.  
Qed.

Theorem mult_0_l : 
  forall n:nat, 
  0 * n = 0.
Proof.
  intros n. 
  reflexivity.  
Qed.

Theorem plus_id_example : 
  forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros * H.
  rewrite H.
  reflexivity.  
Qed.


(** Упраженение  *)

Theorem plus_id_exercise : 
  forall n m o : nat,
  n = m -> 
  m = o -> 
  n + m = m + o.
Proof.
intros *.
intros H1 H2.
rewrite H1.
rewrite H2.
reflexivity.
Qed.


Theorem mult_0_plus : 
  forall n m : nat,
  (0 + n) * m = n * m.
Proof.
intros *.
reflexivity.
Qed.

Theorem mult_S_1 : 
  forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
intros *.
intros H.
rewrite H.
reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry : 
  forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : 
  forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  destruct n as [| m ].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : 
  forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative : 
  forall b c, 
  andb b c = andb c b.
Proof.
    intros b c. 
    destruct b.
    - destruct c.
      + reflexivity.
      + reflexivity.
    - destruct c.
      + reflexivity.
      + reflexivity.
Qed.

Theorem andb_commutative' : 
  forall b c, 
  andb b c = andb c b.
Proof.
  intros b c. 
  destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.


Theorem andb3_exchange :
  forall b c d, 
  andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. 
  destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : 
  forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [| n ].
  - reflexivity.
  - reflexivity.  
Qed.

Theorem andb_commutative'' :
  forall b c, 
  andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Упражнение *)

Theorem andb_true_elim2 : 
  forall b c : bool,
  andb b c = true -> 
  c = true.
Proof.
intros [] [] H; rewrite <- H; reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : 
  forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. 
  destruct n as [| m ].
  - reflexivity.
  - reflexivity.
Qed.

(* пример неудачной функции *)

(*
Fixpoint plusx (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (plusx (pred n) m)
  end.
*)

(** Упражнения *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros * H b.
  repeat rewrite (H b). 
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros * H1 b.
  rewrite (H1 b).
  rewrite (H1 (negb b)).
  case b; reflexivity.
  (* построить доказательство *)
Qed.
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros * H.
  case b, c; simpl in H;try reflexivity; rewrite H; reflexivity.

  (* построить доказательство *)
Qed.