Require Import EqdepFacts.
Require Import VectorDef.

Inductive hoge : Set :=
| foo : nat -> hoge
| bar : forall n, VectorDef.t hoge n -> hoge.


Goal forall n v1 v2, bar n v1 = bar n v2 -> v1 = v2.
Proof.
  intros.
  inversion H.
  apply (Eqdep_dec.inj_pair2_eq_dec _ Arith.Peano_dec.eq_nat_dec) in H1.
  assumption.
Qed.
