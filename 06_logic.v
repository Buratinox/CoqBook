(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

(** . *)

Definition dva_plus_dva : Prop := 2 + 2 = 4.

Theorem proof_dva_plus_dva :
  dva_plus_dva.
Proof. 
	reflexivity.  
Qed.

Theorem proof__dva_plus_dva : 
	2 + 2 = 4.
Proof. 
	reflexivity.
Qed.

(**  *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, 
	f x = f y 
		-> x = y.

Lemma succ_inj : 
	injective S.
Proof.
  intros n m H.
	inversion H.
	reflexivity.
Qed.

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(* Logical Connectives *)

(** Conjunction *)

Example and_example : 
	3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : 
	forall A B : Prop, 
	A -> B -> A /\ B.
Proof.
  intros A B HA HB. 
	split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 
	3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, 
	n + m = 0 
		-> n = 0 /\ m = 0.
Proof.
  (*  *) Admitted.

Lemma and_example2 :
  forall n m : nat, 
	n = 0 /\ m = 0 
		-> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, 
	n = 0 
		-> m = 0 
		-> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : 
	forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (*  *) Admitted.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP. 
Qed.

Theorem and_assoc : 
	forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  (*  *) Admitted.

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(** Disjunction *)

Lemma or_example :
  forall n m : nat, 
	n = 0 \/ m = 0 
		-> n * m = 0.
Proof.
  intros n m [ Hn | Hm ].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : 
	forall A B : Prop, 
	A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, 
	n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, 
	n * m = 0 
		-> n = 0 \/ m = 0.
Proof.
  (*  *) Admitted.

Theorem or_commut : 
	forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  (*  *) Admitted.

(* ================================================================= *)
(** ** Falsehood and Negation *)

Module MyNot.

Definition not (P : Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

Theorem ex_falso_quodlibet : 
	forall P:Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra. 
Qed.

Fact not_implies_our_not : 
	forall P : Prop,
  ~ P 
		-> (forall Q : Prop, P -> Q).
Proof.
  (*  *) Admitted.

Theorem zero_not_one : ~ (0 = 1).
Proof.
  intros contra.
	inversion contra.
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros contra.
	inversion contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H.
	destruct H. 
Qed.

Theorem contradiction_implies_anything : 
	forall P Q : Prop,
  (~ P /\ P) -> Q.
Proof.
  intros P Q [ HNA HP ]. unfold not in HNA.
  apply HNA in HP. destruct HP. 
Qed.

Theorem double_neg : 
	forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. 
	unfold not. 
	intros G. 
	apply G. 	
	apply H. 
Qed.

Theorem contrapositive : 
	forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (*  *) Admitted.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (*  *) Admitted.

Theorem not_true_is_false : 
	forall b : bool,
  b <> true 
		-> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : 
	forall b : bool,
  b <> true 
		-> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.             
    apply H. reflexivity.
  - reflexivity.
Qed.

(** ** Truth *)

Lemma True_is_true : True.
Proof. 
	apply I. 
Qed.

(** ** Logical Equivalence *)

Module MyIff.

Definition iff (P Q : Prop) := 
	(P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : 
	forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB. 
Qed.

Lemma not_true_iff_false : 
	forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem iff_refl : 
	forall P : Prop,
  P <-> P.
Proof.
  (*  *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (*  *) Admitted.

Theorem or_distributes_over_and : 
	forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (*  *) Admitted.

Lemma mult_0 : 
	forall n m, 
	n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, 
	P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** Existential Quantification *)


Lemma four_is_even : 
	exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : 
	forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (*  *) Admitted.

Theorem dist_exists_or : 
	forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (*  *) Admitted.

(** Programming with Propositions *)

Require Export List.
Import ListNotations.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : 
	In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, 
	In n [2; 4] 
		->		exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l 
		->		In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (*  *) Admitted.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (*  *) Admitted.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (*  *). Admitted.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (*  *) Admitted.

(** Applying Theorems to Arguments *)

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

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

Lemma plus_comm3 :
  forall x y z, 
	x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
Abort.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.