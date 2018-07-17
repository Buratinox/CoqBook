(* Inductively Defined Propositions *)

Require Export Logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).

Theorem ev_4 : 
  even 4.
Proof. 
  apply ev_SS. 
  apply ev_SS. 
  apply ev_0. 
Qed.


Theorem ev_4' : 
  even 4.
Proof. 
  apply (ev_SS 2 (ev_SS 0 ev_0)). 
Qed.

Theorem ev_plus4 : 
  forall n : nat, 
  even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem ev_double : 
  forall n : nat,
  even (double n).
Proof.
  (* доказать *) Admitted.

Theorem ev_minus2 : 
  forall n : nat,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E']; simpl.
  - apply ev_0.
  - apply E'.
Qed.

Theorem ev_minus2' : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E']; simpl.
  - apply ev_0.
  - apply E'.
Qed.

Theorem evSS_even :
  forall n : nat,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  assumption.
Qed.

Theorem evSS_even1 : 
  forall n : nat,
  even (S (S n)) -> even n.
Proof.
    (* доказать *) Admitted.

Theorem one_not_even : 
  ~ even 1.
Proof.
  intros H. 
  inversion H. 
Qed.

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
    (* доказать *) Admitted.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
    (* доказать *) Admitted.


Lemma ev_even_firsttry : 
  forall n : nat,
  even n -> exists k, n = double k.
Proof.
  intros n E. 
  inversion E as [| n' E']; simpl.
  - exists 0. simpl. reflexivity.
  - assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I.
Admitted.

Lemma ev_even : 
  forall n : nat,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : 
  forall n : nat,
  even n <-> exists k, n = double k.
Proof.
  intros n. 
  split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : 
  forall n m : nat, 
  even n -> even m -> even (n + m).
Proof.
    (* доказать *) Admitted.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).


Theorem ev'_even : 
  forall n : nat, 
  ev' n <-> even n.
Proof.
    (* доказать *) Admitted.


Theorem ev_ev__even : 
  forall n m : nat,
  even (n + m) -> even n -> even m.
Proof.
    (* доказать *) Admitted.


Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
    (* доказать *) Admitted.


Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.  
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. 
  apply le_S. 
  apply le_S. 
  apply le_n.  
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. 
  inversion H. 
  inversion H2.  
Qed.

End Playground.

Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).

(* предикаты на числах *)

Inductive square : nat -> nat -> Prop :=
| sq : forall n : nat, square n (n * n)
.

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall n : nat, next_nat n (S n)
.

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall n : nat, even (S n) -> next_even n (S n)
| ne_2 : forall n : nat, even (S (S n)) -> next_even n (S (S n))
.



(** придумать свое определение какого-нибудь свойства чисел *)

(** придумать свое определение какого-нибудь свойства чисел, 
    которое никогда не выполняется *)

Lemma le_trans : 
  forall m n o, 
  m <= n -> n <= o -> m <= o.
Proof.
    (* доказать *) Admitted.

Theorem O_le_n : 
  forall n,
  0 <= n.
Proof.
    (* доказать *) Admitted.

Theorem n_le_m__Sn_le_Sm : 
  forall n m,
  n <= m -> S n <= S m.
Proof.
    (* доказать *) Admitted.

Theorem Sn_le_Sm__n_le_m : 
  forall n m,
  S n <= S m -> n <= m.
Proof.
    (* доказать *) Admitted.

Theorem le_plus_l : 
  forall a b,
  a <= a + b.
Proof.
    (* доказать *) Admitted.

Theorem plus_lt : 
  forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
    (* доказать *) Admitted.

Theorem lt_S : 
  forall n m,
  n < m ->
  n < S m.
Proof.
    (* доказать *) Admitted.

Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>	match m with
     		  | O => false
      		| S m' => leb n' m'
      	  end
end.

Theorem leb_complete : 
  forall n m,
  leb n m = true -> n <= m.
Proof.
    (* доказать *) Admitted.

Theorem leb_correct : 
  forall n m,
  n <= m ->
  leb n m = true.
Proof.
    (* доказать *) Admitted.


Theorem leb_true_trans : 
  forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
    (* доказать *) Admitted.

(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : 
  forall n m,
  leb n m = true <-> n <= m.
Proof.
    (* доказать *) Admitted.

Module R.


Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Какие высказывания доказуемы?
      - [R 1 1 2]
      - [R 2 2 6]

    - Если мы удалим конструкторы с4 или c5, 
      изменится ли множество доказуемых выскапзываний?
*)

(** Отношение R кодирует известную функцию. Какую?
Написать её определение *)

Definition fR : nat -> nat -> nat. 
Admitted.

Theorem R_equiv_fR : 
  forall m n o, 
  R m n o <-> fR m n = o.
Proof.
    (* доказать *) Admitted.

End R.


(** Список может быть подсписком другого списка. Например,

      [1;2;3]

    является подсписком списков

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    но не является подсписком списков

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Определить индуктивное свойство одного списка быть подсписком другого.)

    - Доказать, что любой список является своим собственным подсписком.

    - Доказать, что если [l1] подсписок [l2], то [l1] также является подсписком
      [l2 ++ l3].

    - Доказать, что если [l1] подсписок [l2] и [l2] - подсписок [l3], 
      то [l1] подсписок [l3].
 *)

 Inductive RQ : nat -> list nat -> Prop :=
| c1 : RQ 0 nil
| c2 : forall (n : nat) (l : list nat), RQ n l -> RQ (S n) (n :: l)
| c3 : forall (n : nat) (l : list nat), RQ (S n) l -> RQ n l
.

 
 (*
    Какие высказывания доказуемы?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)