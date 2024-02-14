Module NatPlayground.

Inductive nat : Type := 
| O
| S (n:nat).

End NatPlayground.

Fixpoint even (n:nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => even n'
  end.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m:nat) : nat :=
  match n with
  | 0 => 0
  | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | 0, _ => 0
  | S _, 0 => n
  | S n', S m' => minus n' m'
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.

Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | 0 => match m with
        | 0 => true
        | S m' => false
        end
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
  end.


Fixpoint leb (n m: nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            |S m' => leb n' m'
            end
  end.

Example test_leb1 : leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Compute leb 2 2.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Notation "x <=? y" := (leb x y) (at level 870) : nat_scope.

Theorem plus_0_n : forall n:nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall m n:nat,
  n=m -> n + m = m + m.
  Proof. intros m n. intros H. rewrite <- H. reflexivity. Qed.

Check plus_id_example.

Theorem mult_n_0_m_0 : forall p q:nat,
  (0 * p) + (0 * q) = 0.
Proof. intros p q.
        Check mult_0_l.
        rewrite -> mult_0_l.
        rewrite -> mult_0_l.
        simpl. reflexivity. Qed.

(* Case analysis *)

Theorem plus_1_neq_0_firsttry :
  forall n:nat, (n +1) =? 0 = false.
Proof. intros n. simpl. Abort.

Theorem plus_1_neq_0_firsttry :
  forall n:nat, (n +1) =? 0 = false.
Proof. intros n.
       destruct n as [|n'] eqn:E.
       - reflexivity.
       - Print eqb. simpl. reflexivity.
Qed.

(**####################################################################################################################*)

(*Induction*)

Theorem eqb_involutive :
  forall b:bool, negb( negb b) = b.
  Proof.
    intros b. destruct b.
      -reflexivity.
      -reflexivity.
  Qed.

Theorem andb_commutative :
  forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
      simpl. destruct c.
        simpl. reflexivity.
        reflexivity.
      simpl. destruct c.
        reflexivity.
        reflexivity.
  Qed.

Theorem andb_commutative' :
  forall b c, andb b c = andb c b.
  Proof.
    intros [] [].
      -reflexivity.
      -reflexivity.
      -reflexivity.
      -reflexivity.
  Qed.
      
Theorem plus_1_neq_0_firsttry' :
  forall n:nat, (n +1) =? 0 = false.
Proof. intros [|n'].
        -reflexivity.
       - reflexivity.
Qed.

Theorem add_0_r_firsttry :
  forall n:nat, n+0 = n.
Proof.
  intros n. simpl. destruct n as [|n'].
    -reflexivity.
    -Abort.

Theorem add_0_r_firsttry :
  forall n:nat, n+0 = n.
Proof.
  intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem minus_n_m :
  forall n, minus n n = 0.
Proof.
  intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.

Lemma add_S_1 : forall n:nat,
  S n = n + 1.
  Proof.
    intros n. induction n.
      reflexivity.
      simpl. rewrite IHn. reflexivity.
Qed.

Lemma add_S : forall n m:nat,
  S( n + m ) = n + (S m).
Proof.
  intros n m. induction n.
    -reflexivity.
    -simpl. rewrite IHn. reflexivity.
Qed.


Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n.
    -rewrite add_0_r_firsttry. reflexivity.
    -simpl. rewrite IHn. rewrite add_S.
      reflexivity.
Qed.

(**################################################################################*)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [|n'].
    - reflexivity.
    - rewrite <- IHn'. simpl. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m: nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m. assert ( H : n + 0 + 0 = n ).
    { rewrite add_comm. simpl.
      rewrite add_comm. simpl.
      reflexivity. }
      rewrite H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert( H : n + m = m + n).
    { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

(*Lists*)

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Definition fst (p:natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p:natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (p:natprod) : nat :=
  match p with
  | (x, y) => x
  end.

Definition snd' (p:natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p:natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall n m : nat,
  (n,m) = (fst (n,m), snd (n,m)).
Proof. intros m n. simpl. reflexivity.
Qed.

Theorem surjective_pairing_stuck :
  forall (p:natprod),
    p = (fst p, snd p).
  Proof. intros p. destruct p. reflexivity.
Qed.

Inductive natlist : Type :=
| nil 
| cons (n:nat) (l:natlist).

Notation "x :: l" := (cons x l)
                        (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Check [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  |0 => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  |nil => 0
  |cons h t => S (length t)
  end.

Fixpoint length' (l:natlist) : nat :=
  match l with
  | [] => 0
  | h :: t => 1 + length' t
  end.

Fixpoint nonzeros (l:natlist) : nat :=
  match l with
  | nil => 0
  | cons 0 t => nonzeros t
  | cons h t => S (nonzeros t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                      (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Fixpoint foo (n:nat) : natlist :=
  match n with
  | 0 => nil
  | S n' => n :: (foo n')
  end.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
    Proof. intros l. reflexivity.
Qed.

(**######################################################################################################################################################*)

Theorem tl_length_pred : forall l:natlist,
    pred (length l) = length (tl l).
Proof.
  intros l. destruct l.
    - reflexivity.
    - reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1.
    - reflexivity.
    - simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: l => (rev l) ++ [h]
  end.

Theorem app_length : forall l1 l2:natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2. induction l1.
    - reflexivity.
    - simpl. rewrite <- IHl1. reflexivity.
Qed.

Theorem rev_length : forall l:natlist,
  length(rev l) = length l.
Proof.
  intros l. induction l.
    - reflexivity.
    - simpl. rewrite app_length. rewrite IHl. rewrite add_comm. reflexivity.
  Qed.

(**Search(?x + ?y = ?y + ?x)*)

Fixpoint nth_bad (l:natlist) (n:nat) : nat := 
  match l with
  | nil => 42 (*bad!!*)
  | a :: l' => match n with
                | 0 => a
                | S n' => nth_bad l' n'
                end
  end.

  Inductive natoption : Type :=
    | Some (n:nat)
    | None.

  Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => match n with
                | 0 => Some a
                | S n' => nth_error l' n'
                end
  end.

(**#########################################################################################################*)
(*Partial Maps*)

Inductive id : Type :=
| Id (n:nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Inductive partial_map : Type :=
| empty
| record (i:id) (v:nat) (m:partial_map).

Definition update (d:partial_map) (x:id) (value:nat) : partial_map :=
  record x value d.

Fixpoint find (x:id) (d:partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y then Some v
                        else find x d'
  end.

  Theorem quiz1 : forall (d: partial_map) (x : id) ( v:nat),
    find x (update d x v) = Some v.
  Proof.
    intros. simpl. induction x. simpl. rewrite eqb_refl. reflexivity. Qed.

  (**#########################################################################################################################*)
  