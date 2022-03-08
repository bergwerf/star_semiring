From stars Require Import definitions.

Ltac lift_distr H := intros x y z; symmetry; apply H.
Ltac auto_resolve := repeat split; c.

(*** Arithmetic of Boolean logic. *)
Section Boolean.

Global Instance : Equiv bool := eq.
Global Instance : Zero bool := false.
Global Instance : One bool := true.
Global Instance : Add bool := orb.
Global Instance : Mul bool := andb.
Global Instance : Star bool := λ _, 1.

Global Instance : Star_Semiring bool.
Proof. repeat split; repeat intros []; cbn; done. Qed.

End Boolean.

(*** Arithmetic of Peano numbers. *)
Section Natural.

Global Instance : Equiv nat := eq.
Global Instance : Zero nat := 0%nat.
Global Instance : One nat := 1%nat.
Global Instance : Min nat := Nat.min.
Global Instance : Add nat := Nat.add.
Global Instance : Mul nat := Nat.mul.

Global Instance : Assoc (=) min := Nat.min_assoc.
Global Instance : Comm (=) min := Nat.min_comm.
Global Instance : LeftAbsorb (=) 0 min := Nat.min_0_l.
Global Instance : RightAbsorb (=) 0 min := Nat.min_0_r.
Global Instance : LeftDistr (=) add min. lift_distr Nat.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add min. lift_distr Nat.add_min_distr_r. Qed.

Global Instance : Assoc (=) add := Nat.add_assoc.
Global Instance : LeftId (=) 0 add := Nat.add_0_l.
Global Instance : RightId (=) 0 add := Nat.add_0_r.
Global Instance : Comm (=) add := Nat.add_comm.
Global Instance : Assoc (=) mul := Nat.mul_assoc.
Global Instance : LeftId (=) 1 mul := Nat.mul_1_l.
Global Instance : RightId (=) 1 mul := Nat.mul_1_r.
Global Instance : Comm (=) mul := Nat.mul_comm.
Global Instance : LeftAbsorb (=) 0 mul := Nat.mul_0_l.
Global Instance : RightAbsorb (=) 0 mul := Nat.mul_0_r.
Global Instance : LeftDistr (=) mul add := Nat.mul_add_distr_l.
Global Instance : RightDistr (=) mul add := Nat.mul_add_distr_r.

Global Instance : Comm_Semigroup nat (=) min. auto_resolve. Qed.
Global Instance : Semiring nat. auto_resolve. Qed.

End Natural.

(*** Arithmetic of binary numbers. *)
Section Positive.

Global Instance : Equiv N := eq.
Global Instance : Zero N := 0%N.
Global Instance : One N := 1%N.
Global Instance : Min N := N.min.
Global Instance : Add N := N.add.
Global Instance : Mul N := N.mul.

Global Instance : Assoc (=) min := N.min_assoc.
Global Instance : Comm (=) min := N.min_comm.
Global Instance : LeftAbsorb (=) 0 min := N.min_0_l.
Global Instance : RightAbsorb (=) 0 min := N.min_0_r.
Global Instance : LeftDistr (=) add min. lift_distr N.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add min. lift_distr N.add_min_distr_r. Qed.

Global Instance : Assoc (=) add := N.add_assoc.
Global Instance : LeftId (=) 0 add := N.add_0_l.
Global Instance : RightId (=) 0 add := N.add_0_r.
Global Instance : Comm (=) add := N.add_comm.
Global Instance : Assoc (=) mul := N.mul_assoc.
Global Instance : LeftId (=) 1 mul := N.mul_1_l.
Global Instance : RightId (=) 1 mul := N.mul_1_r.
Global Instance : Comm (=) mul := N.mul_comm.
Global Instance : LeftAbsorb (=) 0 mul := N.mul_0_l.
Global Instance : RightAbsorb (=) 0 mul := N.mul_0_r.
Global Instance : LeftDistr (=) mul add := N.mul_add_distr_l.
Global Instance : RightDistr (=) mul add := N.mul_add_distr_r.

Global Instance : Comm_Semigroup N (=) min. auto_resolve. Qed.
Global Instance : Semiring N. auto_resolve. Qed.

End Positive.

(*** Arithmetic of minimum and addition. *)
(* Tropical is a reference to the climate of Brazil, where Imre Simon lived. *)
(* Imre Simon (1943-2009) founded the topic of tropical mathematics. *)
Section Tropical.

Variable X : Type.
Context `{Equiv X, Equivalence X (≡), Min X, Add X, Zero X}.
Context `{Comm_Semigroup X (≡) min, Monoid X (≡) add 0}.
Context `{LeftAbsorb X (≡) 0 min, RightAbsorb X (≡) 0 min}.
Context `{LeftDistr X (≡) add min, RightDistr X (≡) add min}.

Inductive trop := Tropical (x : X) | Infinity.

Global Instance : Equiv trop := λ a b,
  match a, b with
  | Tropical x, Tropical y => x ≡ y
  | Infinity, Infinity => True
  | _, _ => False
  end.

Global Instance : Zero trop := Infinity.
Global Instance : One trop := Tropical 0.

Global Instance : Add trop :=
  λ a b, match a, b with
  | Infinity, _ => b
  | _, Infinity => a
  | Tropical x, Tropical y => Tropical (min x y)
  end.

Global Instance : Mul trop :=
  λ a b, match a, b with
  | Infinity, _ => Infinity
  | _, Infinity => Infinity
  | Tropical x, Tropical y => Tropical (x + y)
  end.

Global Instance trop_star : Star trop :=
  λ _, 1.

Global Instance : Star_Semiring trop.
Proof.
repeat split.
4,9: intros [] [] A [] [] B; cbn in *; try done; rewrite A, B; done.
all: repeat intros []; cbn; try done; f_equal. apply Equivalence_Transitive.
apply assoc; c. apply comm; c. apply assoc; c.
apply left_id; c. apply right_id; c.
Qed.

End Tropical.

Arguments Tropical {_}.
Arguments Infinity {_}.
