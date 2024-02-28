Inductive natlist : Type :=
  | nat_nil
  | nat_cons (b:nat) (l:natlist).

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b:bool) (l:boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x:X) (l:list X).

Check list.

Check nil nat.

Check cons nat 2 (cons nat 1 (nil nat)).

Check cons bool true (nil bool).

Fixpoint repeat (X:Type) (x:X) (count:nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Compute (repeat nat 10 3).
Compute (repeat bool true 4).

Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat' _ x count')
  end.

  Check repeat'.  
  Check repeat.

Check cons _ 1 (nil _).
  
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Check cons 1 nil.

Fixpoint repeat''' {X:Type} (x:X) (count:nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X:Type} (l1 l2:list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Check [1;2;3].
Check [true;false].
Check [].

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
 Compute (rev [1;2;4]).

Fixpoint length {X:Type} (l:list X) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Compute length [true;false;false].

 Fail Definition mynil : list nat := nil nat.

 Fail Definition mynil : nat := nil.

 Definition mynil := @nil nat.

 Compute cons 1 nil.

 Compute @cons nat 1 (@nil nat).

 Check [1;2;3].

 Check [[1]; nil].

 Inductive prod {X Y:Type} : Type :=
  | pair (x:X) (y:Y).

Check pair.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (@prod X Y) : type_scope.

Definition fst {X Y:Type} (p : X * Y) : X :=
  match p with
  | ( x , y ) => x
  end.

Definition snd {X Y:Type} (p : X * Y) : Y :=
  match p with
  | ( x , y ) => y
  end.

Fixpoint combine {X Y:Type} (lx:list X) (ly:list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x::tx, y::ty => ( x , y ) :: (combine tx ty)
  end.

Inductive option (X:Type) : Type :=
  | Some (x:X)
  | None.

Arguments Some {X}.
Arguments None {X}.

Fixpoint nth_error {X:Type} (l:list X) (n:nat) : @option X :=
  match l with
  | nil => None
  | a::l' => match n with
            | O => Some a
            | S n' => nth_error l' n'
            end
  end.

Compute nth_error [1;2] 1.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times nat.

Definition subtract2 (n:nat) : nat :=
  n - 2.

Compute doit3times subtract2 10.

Fixpoint filter {X:Type} (test:X->bool) (l:list X) : list X :=
  match l with
  | nil => nil
  | h::t => if test h then h::(filter test t) 
            else (filter test t)
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Compute filter even [1;2;3;4;5;6;7;8;9;10].

Require Nat.
Import Nat.

Definition length_is_1 {X:Type} (l:list X) : bool :=
  (length l) =? 1.

Example test_filter2 : filter length_is_1 [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
  Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers' : countoddmembers' [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.

(* Anonymous Functions *)

Definition squareit (n:nat) : nat :=
  n * n.

Example square_three_times : doit3times squareit 2 = 256.
  Proof. reflexivity. Qed.

Example square_three_times' :  doit3times (fun n => n * n) 2 = 256.
  Proof. reflexivity. Qed.

Example test_filter' : filter (fun l => (length l) =? 1) [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
  Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : list Y :=
  match l with
  | [] => []
  | h::t => (f h)::(map f t)
  end.

Example test_map : map (fun x => x + 2) [1;3;5;0] = [3;5;7;2].
  Proof. reflexivity. Qed.

Example test_map' : map odd [1;3;2;5;0] = [true;true;false;true;false].
  Proof. reflexivity. Qed.

Example test_map'' :
  map (fun n => [even n; odd n]) [2;1;3;4;5] = [[true;false]; [false;true]; [false;true]; [true;false]; [false;true]].
  Proof. reflexivity. Qed.

Inductive natorbool : Type :=
| makeNat (n:nat)
| makeBool (b:bool).

Definition option_map {X Y:Type} (f:X->Y) (xo:option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f:X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | [] => b
  | h::t => f h (fold f t b)
  end.

Compute fold plus [1;2;3;4] 0.

Check fold andb.

Example fold_example1 : fold andb [true;true;false;true] true = false.
  Proof. reflexivity. Qed.

Example fold_example2 : fold mult [1;2;3;4] 1 = 24.
  Proof. reflexivity. Qed.


Definition constfun {X:Type} (x:X) : nat-> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition make_function {X:Type} (x:X) : nat -> nat :=
  squareit.

Fixpoint nest {X:Type} (n:nat) (f:X -> X) : X -> X :=
  fun x => match n with
           | O => x
           | S n' => f (nest n' f x)
           end.

(**#########################################################################################################*)

(* Tatics *)

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
  Proof. intros. apply H. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
  Proof. intros. apply H0. apply H. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  ( forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
  Proof. intros. apply H0. apply H. Qed.

Theorem eqb_0_l : forall n:nat,
    0 =? n = true -> n = 0.
Proof.
  intros n. destruct n.
    - simpl. reflexivity.
    - simpl. discriminate.
Qed.

Theorem blah : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros. rewrite H. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m ->  S n = S m.
    Proof.
      intros. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b:bool),
  (S n) =? (S m) = b -> n =? m = b.
  Proof.
    intros. simpl in H. apply H. Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  p = q.
Proof.
  intros. symmetry in H0. apply H. apply H0. Qed.

Fixpoint double (n:nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
  double n = double m -> n = m.
  Proof.
    intros n m. induction n as [| n' IHn'].
    - simpl. intros eq. destruct m as [| m'] eqn:E.
      + reflexivity.
      + discriminate.
    - intros eq. destruct m as [| m'] eqn:E.
      + discriminate.
      + apply f_equal. Abort.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. intros. destruct m.
    + reflexivity.
    + discriminate.
  - intros. simpl. destruct m.
    + discriminate.
    + f_equal. apply IHn'. simpl in H. injection H as H1. apply H1. Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
    intros n m.
    generalize dependent m.
    induction n as [| n' IHn'].
    - intros. induction m.
      -- reflexivity.
      -- simpl in H. discriminate.
    - intros. induction m.
      -- simpl in H. discriminate.
      -- simpl in H. apply IHn' in H. apply eq_implies_succ_equal. apply H.
Qed.

Definition square n := n * n.

Definition foo (x:nat) : nat := 5.

Fact silly_fact_1 : forall m,
  foo m + 1 = foo (m + 1) + 1.
  Proof. intros. reflexivity. Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m,
  bar m + 1 = bar (m + 1) + 1.
  Proof. intros. unfold bar. destruct m.
  - reflexivity.
  - reflexivity.
Qed.