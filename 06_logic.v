(** * Logic: Logic in Coq *)

Check (3 = 3).
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

(** . *)

Definition dva_plus_dva : Prop := (2 + 2 = 4).

Theorem proof_dva_plus_dva :
  dva_plus_dva.
Proof. 
	unfold dva_plus_dva. reflexivity.  
Qed.

Theorem proof__dva_plus_dva : 2 + 2 = 4.
Proof. 
	reflexivity.
Qed.

Check proof__dva_plus_dva.
Check (2 + 2 = 4).

(**  *)

Definition is_three (n : nat) : Prop := n = 3.
Check is_three.
(* ===> nat -> Prop *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma true_false : 
  true <> false.
Proof.
  discriminate.
Qed.

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

Theorem plus_n_O : 
  forall n : nat, 
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
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

Example and_exercise :
  forall n m : nat, 
	n + m = 0 
		-> n = 0 /\ m = 0.
Proof.
  intros * H. split.
  induction n. reflexivity. discriminate. 
  induction m. reflexivity. rewrite plus_comm in H.
  discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, 
	n = 0 /\ m = 0 
		-> n + m = 0.
Proof.
  intros * H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, 
  n = 0 /\ m = 0 
    -> n + m = 0.
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
  forall n m : nat, 
  n + m = 0 
    -> n * m = 0.
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
  intros P Q HPQ.
  destruct HPQ as [HP HQ].
  apply HP.  
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
intros P Q HPQ.
destruct HPQ as [HP HQ].
apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HQ HP]. split; assumption.
Qed.

Theorem and_assoc : 
	forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  repeat split; assumption.
Qed.
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
	B -> A \/ B.
Proof.
  intros A B HA.
  right.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, 
	n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, 
	n * m = 0 
		-> n = 0 \/ m = 0.
Proof.
  intros * H.
  destruct n as [|n].
  -left. reflexivity.
  -right. induction m. reflexivity.
  discriminate.
Qed.

Theorem or_commut : 
	forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q HPQ.
  destruct HPQ. right. assumption.
  left. apply H.
Qed.

Theorem qwerty :
forall x y z : Prop,
(x /\ (y /\ z)) <->((x /\ y) /\ z).
Proof.
  intros *.
  split; intros H.
  -destruct H as [ Hx [ Hy Hz ] ]. repeat split; assumption.
  -destruct H as [ [H1 H3] H2 ]. repeat split; assumption.
Qed.
(* ================================================================= *)
(** ** Falsehood and Negation *)

Module MyNot.

Definition not (P : Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

Theorem ex_falso_quodlibet : 
	forall P : Prop,
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
  intros P nP Q Hp.
  apply nP in Hp. 
  destruct Hp. 
Qed.

Theorem zero_not_one : (0 <> 1).
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
	assumption.
Qed.

Theorem not_False' :
  forall P : Prop,
  P
    -> ~ ~ P.
Proof.
  unfold not. intros.
	apply H0. apply H.
Qed.

Theorem contradiction_implies_anything : 
	forall P : Prop,
  ~ (~ P /\ P).
Proof.
  unfold not.
  intros P [ nHP HP ]. 
  apply (nHP HP).
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
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q H1. unfold not. intros H2. intros. apply H2 in H1. destruct H1.
  apply H.
Qed.

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

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
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
  intros P. split; intros; apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2. split. 
  -intros. apply H2. apply H1. apply H. 
  -intros. apply H1. apply H2. apply H.
Qed.

Theorem or_distributes_over_and : 
	forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split; intros.
  - destruct H. 
    + split; left; assumption.
    + destruct H. split; right; assumption. 
  - destruct H. 
    destruct H. 
    + left; assumption.
    + destruct H0.
      * left; assumption.
      * right; split; assumption.   
Qed.

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

Theorem exists_example_2 : 
  forall n,
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
  intros P X. intros. unfold not. intros [x f]. apply f. 
  apply H.
Qed.

Theorem dist_exists_or : 
	forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros P Q. intros. split; intros.
  - destruct H as [x [H1|H2]];[left|right]; exists x; assumption.
  - destruct H; destruct H; exists x; [left|right]; assumption.
Qed.

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
  intros n [ H1 | [ H2 | H3 ] ].
  - exists 1. simpl. rewrite H1. reflexivity.
  - exists 2. simpl. rewrite H2. reflexivity.
  - exfalso. assumption. 
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l 
		->		In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros; assumption.
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros*. split; intros.
  { induction l.
    - simpl in*. exfalso. assumption.
    - destruct H. 
      + exists a. split. assumption. left. reflexivity.
      + destruct (IHl H) as [ b [ H1 H2]].
        exists b. split. assumption. right. assumption.
  }
  { destruct H as [ a [ H1 H2 ] ].
    induction l; simpl in *. assumption.
    destruct H2 as [ H2 | H3 ]. subst. 
    - left. reflexivity.
    - right. apply IHl. assumption.
  }
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros *. split; intros.
  -induction l. simpl in *. right. assumption.
  destruct H. subst. left. simpl. left. reflexivity. 
  apply IHl in H. destruct H. left. simpl. right. assumption.
  right. assumption.
  -induction l. simpl in *. destruct H. destruct H. assumption.
  simpl. destruct H. destruct H. subst. left. reflexivity.
  right. apply IHl. left. assumption. right. apply IHl. 
  right. assumption.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
match l with
| [] => True
| h :: t => P h /\ All P t
end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros *. split; intros.
  -induction l; simpl in *. reflexivity. split.
  apply H. left. reflexivity. apply IHl. intros. apply H. right.
  assumption.
  - induction l. 
    + simpl in *; exfalso. assumption. 
    + simpl in *. destruct H. 
      destruct H0. 
      * subst. assumption. 
      * apply IHl. assumption. assumption.
Qed.
