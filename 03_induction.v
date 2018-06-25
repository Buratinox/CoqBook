(** * Proof by Induction *)

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
  (* доказать утверждение *) Admitted.

Theorem plus_n_Sm : 
  forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* доказать утверждение *) Admitted.

Theorem plus_comm : 
  forall n m : nat,
  n + m = m + n.
Proof.
  (* доказать утверждение *) Admitted.

Theorem plus_assoc : 
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* доказать утверждение *) Admitted.

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
  (* доказать утверждение *) Admitted.

Fixpoint evenb (n : nat) : bool :=
match n with
| O        	=> true
| S O      	=> false
| S (S m) 	=> evenb m
end.

Definition oddb (n : nat) : bool := negb (evenb n).

Theorem evenb_S : 
  forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* доказать утверждение *) Admitted.


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


Theorem plus_rearrange_firsttry : 
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite (plus_comm n m).
  reflexivity.
Qed.

Theorem plus_rearrange : 
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. 
  reflexivity.
Qed.

Theorem plus_assoc' : 
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. 
  intros n m p. 
  induction n as [| n' IHn']. 
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  
Qed.

Theorem plus_assoc'' : 
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. 
  induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Упражнения *)
Theorem plus_swap : 
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* доказать утверждение *) Admitted.

Theorem mult_comm : 
  forall m n : nat,
  m * n = n * m.
Proof.
  (* доказать утверждение *) Admitted.

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
  (* доказать утверждение *) Admitted.

Theorem zero_nbeq_S : 
  forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* доказать утверждение *) Admitted.

Theorem andb_false_r : 
  forall b : bool,
  andb b false = false.
Proof.
  (* доказать утверждение *) Admitted.

Theorem plus_ble_compat_l : 
  forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  (* доказать утверждение *) Admitted.

Theorem S_nbeq_0 : 
  forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* доказать утверждение *) Admitted.

Theorem mult_1_l : 
  forall n:nat, 
  1 * n = n.
Proof.
  (* доказать утверждение *) Admitted.

Theorem all3_spec : 
  forall b c : bool,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  (* доказать утверждение *) Admitted.


Theorem mult_plus_distr_r : 
  forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* доказать утверждение *) Admitted.

Theorem mult_assoc : 
  forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* доказать утверждение *) Admitted.

Theorem beq_nat_refl : 
  forall n : nat,
  true = beq_nat n n.
Proof.
  (* доказать утверждение *) Admitted.


Theorem plus_swap' : 
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros *.
  replace (n + (m + p)) with ((n + m) + p).
  (* доказать утверждение *) Admitted.