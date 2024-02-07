Inductive day : Type :=
 | monday
 | tuesday
 | wednesday
 | thursday
 | friday
 | saturday
 | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday friday)).

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true
| false.

Definition negb (b:bool) : bool := 
  match b with
  |true => false
  |false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  |true => b2
  |false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1 : (nandb true false) = true.
Proof. simpl. unfold nandb. simpl. reflexivity. Qed.

Check true.

Check (negb true).

Check negb.

Inductive rgb : Type :=
|red
|green
|blue.

Inductive color : Type :=
|black
|white
|primary (p:rgb).

Check (primary red).

Definition monochrome (c:color) : bool :=
  match c with
  |black => true
  |white => true
  |primary p => false
end.

Definition isred (c:color) : bool :=
  match c with
  |black => false
  |white => false
  |primary p => match p with
                |red => true
                |green => false
                |blue => false
                end
  end.

Definition isred' (c:color) : bool := 
  match c with
  |black => false
  |white => false
  |primary red => true
  |primary _ => false
  end.

Definition isred'' (c:color) : bool :=
  match c with
  |primary red => true
  | _ => false
  end.

Compute (isred'' (primary red)).