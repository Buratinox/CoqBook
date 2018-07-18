Inductive eveni : nat -> Prop :=
| evnO : eveni O
| evnS : forall n : nat, eveni n -> eveni (S (S n))
.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O       		=> true
	| S O 			=> false
  | S (S k) 	=> evenb k
  end.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition evend (n : nat) : Prop := 
	exists k : nat, double k = n.

Theorem ev_i_d : 
  forall n : nat,
  eveni n <-> evend n.
Proof.
  intros n. 
  split.
  {	intros E.
  		induction E as [|n' E' IH].
  		-	exists 0. reflexivity.
  		-	destruct IH as [k' Hk'].
    		exists (S k'). rewrite <- Hk'. reflexivity.
	}
  {	intros [k Hk].
		rewrite <- Hk. clear dependent n.
  		induction k; simpl.
  		- apply evnO.
  		- apply evnS. apply IHk.
	}
Qed.

Lemma double_dec :
	forall n,
	(exists k, double k = n) \/ (exists k, S(double k) = n).
Proof.
	intros n. 
	induction n. 
	left. exists 0. simpl. reflexivity.
	destruct IHn.
	-	right. destruct H. exists x. rewrite H. reflexivity.
	-	left. destruct H. exists (S x). rewrite <- H. simpl. reflexivity.
Qed.

Theorem ind_hyp :
	forall (P : nat -> Prop), 
	P 0 
		-> (forall n, P n -> P (S (S n))) 
		-> (forall n, P (double n)). 
Proof.
	intros P H0 H1 n.
	assert(P (double n) /\ P (S (S (double n)))). 
	{	induction n as [| k ].  
		{	split; simpl.
			{	assumption. }
			{ apply (H1 0). assumption. }
		}
		destruct IHk as [ H2 H3 ]. 
		split; simpl. assumption. 
		apply (H1 (S (S (double k)))).
		assumption.
 	}
	{	destruct H as [H3 H2]. assumption. }
Qed. 

Theorem ev_i_b :
	forall n : nat,
  eveni n <-> evenb n = true.
Proof. 
  intros n. 
	split. 
	{	intros E.
		induction E as [| k E H]; simpl. 
		- reflexivity.
		- assumption.
	}
	{	intros H.
		destruct (double_dec n) as [ Evn | Odd ]. 
		{	destruct Evn as [ k Hk ]. subst.
			apply ind_hyp. 
			{	apply evnO. } 
			{	intros m Hm. apply evnS. assumption. }
		}
		destruct Odd as [ k Hk ]. subst.
		exfalso.
		induction k. 
		{	simpl in *. discriminate. }
		{	induction k. 
			{	simpl in H. discriminate. } 
			{	apply IHk0.
				{	simpl in *. assumption. }
				{	intros H1. apply IHk. simpl in *. assumption. }
			}
		} 
	}
Qed.