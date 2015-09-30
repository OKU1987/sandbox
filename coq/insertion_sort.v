Require Import ssreflect ssrbool ssrnat.
Require Import Recdef.
Open Scope list_scope.
Import List.ListNotations.

Function insert (n : nat) (l : list nat) {measure length l} : list nat :=
  match l with
    | n0::l' =>
      if n <= n0 then
        n::(insert n0 l')
      else n0::(insert n l')
    | [] => [n]
  end.
Proof.
  - auto.
  - auto.
Qed.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
    | n::l' => insert n (insertion_sort l')
    | [] => []
  end.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_singleton : forall n, sorted [n]
| sorted_cons : forall (n1 n2 : nat) (l : list nat),
                  n1 <= n2 ->
                  sorted (n2::l) ->
                  sorted (n1::n2::l).

Lemma insert_preserves_sortedness : forall (n : nat) (l : list nat),
                                      sorted l ->
                                      sorted (insert n l).
Proof.
  intros n l.
  generalize dependent n.
  induction l as [|n0 l]; intro n.
  - rewrite insert_equation.
    constructor.
  - rewrite insert_equation.
    case:ifP => H H0.
    + inversion H0; subst; rewrite insert_equation;
      try move: (IHl n0 H4) => {H4} sorted_insert;
        try rewrite ?insert_equation H3 in sorted_insert|-* ;
        try constructor => // .
    + inversion H0; subst; rewrite insert_equation.
      * constructor.
        case:leqP => // => H1.
        rewrite -H leq_eqVlt H1 orbT // .
        constructor.
      * case:ifP => H1; try constructor; try move: (IHl n H4) => {IHl} H5;
          try rewrite insert_equation H1 in H5 => // .
        case:leqP => // => H2.
        rewrite -H leq_eqVlt H2 orbT // .
Qed.


Lemma insertion_sorts : forall l, sorted (insertion_sort l).
Proof.
  induction l.
  - rewrite /insert. constructor.
  - rewrite /insert-/insert.
    apply (insert_preserves_sortedness _ _ IHl).
Qed.
