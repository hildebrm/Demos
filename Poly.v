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

