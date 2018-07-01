(** Structured Data *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity. 
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros[ n m ]; simpl; reflexivity.
Qed.
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros[ n m ]; simpl; reflexivity.
Qed.

(** * Lists of Numbers *)


Inductive natlist : Set :=
| nil  : natlist
| cons : nat -> natlist -> natlist.


Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "[ ]" := nil.

Notation "n :: l" := (cons n l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
Compute (repeat 7 20).

Fixpoint length (l : natlist) : nat :=
match l with
| [] => O
| n :: l' => S (length l')
end.


Fixpoint app (l1 l2 : natlist) : natlist :=
match l1 with
| []      => l2
| h :: t  => h :: app t l2
end.


Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.


(* ----------------------------------------------------------------- *)
(** *** Exercises *)

Fixpoint nonzeros (l : natlist) : natlist :=
match l with
| nil => nil
| h :: t =>   match h with
              | O   => nonzeros t
              | S _ => h :: nonzeros t
              end
end.

Compute (nonzeros [0;1;0;2;3;0;0]).

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  reflexivity.
Qed.

Fixpoint evenb (n : nat) : bool :=
match n with
| O        	=> true
| S O      	=> false
| S (S m) 	=> evenb m
end.

Definition oddb (n : nat) : bool := negb (evenb n).

Fixpoint oddmembers (l : natlist) : natlist :=
match l with
| nil     => nil
| h :: t  =>  if evenb h 
              then oddmembers t 
              else h :: oddmembers t
end.

Fixpoint oddmembers' (l : natlist) : natlist :=
match l with
| nil     => nil
| h :: t  =>  match evenb h with
              | true => oddmembers t 
              | false => h :: oddmembers t
              end
end.

Example test_oddmembers:
  oddmembers' [0;1;0;2;3;0;0] = [1;3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
match l with
| nil     => O
| h :: t  =>  if oddb h 
              then S (countoddmembers t)
              else countoddmembers t
end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. 
   reflexivity.
Qed.
  
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
  reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1, l2 with
| nil , nil           => nil
| nil , _             => l2
| _ , nil             => l1
| h1 :: t1, h2 :: t2  => h1 :: h2 :: alternate t1 t2
end.

Compute (alternate [1;2;3] [4;5;6]).

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
  reflexivity.
Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
  reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
  reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.

Theorem tl_length_pred : 
  forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.  
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. 
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
match l with 
| nil => nil
| h :: t => (rev t) ++ [h]
end.

Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2 : rev nil = nil.
Proof. reflexivity.  Qed.


Theorem rev_length_firsttry : 
  forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. 
  induction l as [| n l' IHl'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHl'.
Abort.

Theorem app_length : 
  forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. 
  induction l1 as [| n l1' IHl1'].
  - simpl.
    reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
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


Theorem rev_length : 
  forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length. rewrite plus_comm.
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros*.
  induction l; simpl. reflexivity.
  rewrite -> IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros*.
  induction l1; simpl.
  -rewrite app_nil_r. reflexivity.
  - rewrite IHl1. rewrite app_assoc. reflexivity. 
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros*.
  induction l; simpl. reflexivity.
  rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros*.
  induction l1; simpl.
  -rewrite app_assoc. reflexivity.
  -rewrite <- IHl1. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros *.
  induction l1.
  - simpl; reflexivity.
  - induction n as [| n IHn ]; simpl.
    + rewrite IHl1. reflexivity.
    + rewrite IHl1. reflexivity. 
  
Qed.

Fixpoint ravno (n m : nat) : bool :=
match n , m with
|O , O => true
|O , _ => false
|_ , O => false
|S n' , S m' => (ravno n' m')
end.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1 , l2 with
|nil , nil => true
|nil , _ => false
|_ , nil => false
|h1 :: t1 , h2 :: t2 => if ravno h1 h2 
                        then beq_natlist t1 t2
                        else false
end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.

Theorem beq_natlist_refl : 
  forall l : natlist,
  true = beq_natlist l l.
Proof.
  intros *.
  induction l; simpl. reflexivity.
  replace (ravno n n) with true. rewrite IHl. reflexivity.
  induction n; simpl. reflexivity.
  rewrite IHn. reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>	match m with
     		  | O => false
      		| S m' => leb n' m'
      	  end
end.

Theorem ble_n_Sn : 
  forall n : nat,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  
Qed.
