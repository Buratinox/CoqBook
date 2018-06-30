(** * Proof by Induction *)
(*
Inductive bool : Set :=
| true : bool
| false : bool
.
*)
Check bool_ind.

Inductive day : Set :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday
.

Check day_ind.

(*
Inductive nat : Set :=
| O : nat
| S : nat -> nat
.

Check nat_ind.

*)

Theorem plus_n_O_firsttry : 
  forall n : nat,
  n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_O_secondtry : 
  forall n:nat,
  n = n + 0.
Proof.
  intros n. 
  destruct n as [| n'].
  - reflexivity. 
  - simpl.
Abort.

Theorem plus_n_O_thirdtry : 
  forall n : nat, 
  n = n + 0.
Proof.
  apply nat_ind. 
  - reflexivity.
  - intros. simpl. rewrite <- H. reflexivity.
Qed.

Theorem plus_n_O : 
  forall n : nat, 
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : 
  forall n : nat,
  minus n n = 0.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : 
  forall n : nat,
  n * 0 = 0.
Proof.
intros*.
induction n as [| n' IHn']; simpl.
-reflexivity.
-rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_1_l : 
  forall n : nat, 
  1 + n = S n.
Proof.
  intros n. 
  reflexivity.  
Qed.

Theorem plus_n_Sm : 
  forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros *.
induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm : 
  forall n m : nat,
  n + m = m + n.
Proof.
  intros*.
  induction n as [| n' IHn']; simpl.
  -apply plus_n_O.
  -rewrite IHn'. apply plus_n_Sm.
Qed.

Theorem plus_assoc : 
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros*.
induction n as [| n IHn]; simpl.
-reflexivity.
-rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus :
  forall n : nat, 
  double n = n + n .
Proof.
intros*.
induction n as [| n IHn]; simpl.
-reflexivity.
-rewrite IHn. rewrite <- (plus_1_l n). rewrite <- (plus_1_l (n+n)).
rewrite (plus_assoc 1 n n). rewrite (plus_assoc n 1 n). rewrite plus_comm.
rewrite plus_assoc. reflexivity.
Qed.

Fixpoint evenb (n : nat) : bool :=
match n with
| O        	=> true
| S O      	=> false
| S (S m) 	=> evenb m
end.

Definition oddb (n : nat) : bool := negb (evenb n).

Theorem negb_involutive : 
  forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem evenb_S : 
  forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros*. 
  induction n.
  - simpl. reflexivity.
  - assert (H : evenb (S (S n)) = evenb n).
      simpl. reflexivity.
    rewrite H. rewrite IHn. rewrite negb_involutive. reflexivity.
Qed.


Theorem mult_0_plus' : 
  forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H : 0 + n = n). 
    { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_rearrange : 
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite (plus_comm n m).
  reflexivity.
Qed.

(* Упражнения *)
Theorem plus_swap : 
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros*.
  rewrite (plus_assoc n m p). rewrite (plus_comm n m). 
  rewrite (plus_assoc m n p). reflexivity.
Qed.

Theorem mult1 :
forall n : nat,
n * 1 = n.
Proof.
  intros *.
  induction n; simpl; try reflexivity.
  rewrite IHn. reflexivity.
Qed.

Theorem mult_1 :
forall m n : nat,
m * S n = m + m * n.
Proof.
  intros *.
  induction m as [| m IHm]; simpl.
  -reflexivity.
  -rewrite IHm. rewrite plus_assoc. rewrite plus_assoc.
  rewrite (plus_comm n m). reflexivity.
Qed.

Theorem mult_comm : 
  forall m n : nat,
  m * n = n * m.
Proof.
  intros*.
  induction n as [| n' IHn']; simpl.
  - apply mult_0_r.
  - rewrite <- IHn'. rewrite mult_1. reflexivity.
Qed.

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


Theorem leb_refl : 
  forall n:nat,
  true = leb n n.
Proof.
  intros*.
  induction n; simpl. reflexivity.
  rewrite IHn. reflexivity.
Qed.

Theorem zero_nbeq_S : 
  forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros*.
  induction n; simpl; reflexivity.
Qed.

Theorem S_nbeq_0 : 
  forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros*.
  induction n; simpl; reflexivity.
Qed.

Theorem plus_ble_compat_l : 
  forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros*.
  induction p; simpl; intros.
  -rewrite H. reflexivity.
  -rewrite IHp. reflexivity. rewrite H. reflexivity.
Qed.

Theorem mult_1_l : 
  forall n:nat, 
  1 * n = n.
Proof.
  intros*.
  induction n; simpl. reflexivity.
  rewrite <- plus_n_O. reflexivity.
Qed.

Theorem mult_plus_distr_r : 
  forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros*.
  induction n; simpl. reflexivity.
rewrite IHn. rewrite plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : 
  forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros *.
  induction n; simpl. reflexivity.
  rewrite IHn. rewrite mult_plus_distr_r. reflexivity.
Qed.

Theorem beq_nat_refl : 
  forall n : nat,
  true = beq_nat n n.
Proof.
  intros*.
  induction n; simpl. reflexivity.
  rewrite IHn. reflexivity.
Qed.

Theorem plus_swap' : 
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros *.
  replace (n + (m + p)) with ((n + m) + p); rewrite plus_assoc.
  -rewrite (plus_comm n m). reflexivity.
  -reflexivity.
Qed.