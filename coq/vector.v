Section Vector.
  Variable A : Type.
  Variable f : A -> bool.

  Inductive Vec : nat -> Type :=
  | nil : Vec 0
  | cons : forall {n}, A -> Vec n -> Vec (S n).

  Notation "[]" := nil.
  Notation "a :: l" := (cons a l).

  Fixpoint append {n m : nat} (v : Vec n) (v0 : Vec m) : Vec (n + m) :=
    match v with
      | [] => v0
      | a::v' => a::(append v' v0)
    end.

  Fixpoint filter_length {n} (v : Vec n) : nat :=
    match v with
      | [] => O
      | a::v' =>
        if f a then S (filter_length v') else filter_length v'
    end.

  Fixpoint filter {n} (v : Vec n) : Vec (filter_length v) :=
    match v as v0 return Vec (filter_length v0)
    with
      | [] => []
      | a::v' =>
        if f a as b return Vec (if b then S (filter_length v')
                                else filter_length v')
        then a::(filter v')
        else filter v'
    end.
End Vector.
