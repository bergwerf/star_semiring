From stars Require Import definitions.

Ltac lift_distr H := intros x y z; symmetry; apply H.

(*** Arithmetic of Boolean logic. *)
Section Boolean.

Global Instance : Equiv bool := eq.
Global Instance : Zero bool := false.
Global Instance : One bool := true.
Global Instance : Add bool := orb.
Global Instance : Mul bool := andb.
Global Instance : Star bool := λ _, 1.

Local Ltac prove := repeat intros []; cbn; done.

Global Instance : Assoc (=) add. prove. Qed.
Global Instance : LeftId (=) 0 add. prove. Qed.
Global Instance : RightId (=) 0 add. prove. Qed.
Global Instance : Comm (=) add. prove. Qed.
Global Instance : Assoc (=) mul. prove. Qed.
Global Instance : LeftId (=) 1 mul. prove. Qed.
Global Instance : RightId (=) 1 mul. prove. Qed.
Global Instance : Comm (=) mul. prove. Qed.
Global Instance : LeftAbsorb (=) 0 mul. prove. Qed.
Global Instance : RightAbsorb (=) 0 mul. prove. Qed.
Global Instance : LeftDistr (=) mul add. prove. Qed.
Global Instance : RightDistr (=) mul add. prove. Qed.

Global Instance : Monoid bool (=) add 0. Qed.
Global Instance : Comm_Monoid bool (=) add 0. Qed.
Global Instance : Monoid bool (=) mul 1. Qed.
Global Instance : Comm_Monoid bool (=) mul 1. Qed.
Global Instance : Semiring bool. Qed.
Global Instance : Star_Semiring bool. split; prove. Qed.

End Boolean.

(*** Arithmetic of Peano numbers. *)
Section Natural.

Global Instance : Equiv nat := eq.
Global Instance : Zero nat := 0%nat.
Global Instance : One nat := 1%nat.
Global Instance : Min nat := Nat.min.
Global Instance : Add nat := Nat.add.
Global Instance : Mul nat := Nat.mul.

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

Global Instance : Monoid nat (=) add 0. Qed.
Global Instance : Comm_Monoid nat (=) add 0. Qed.
Global Instance : Monoid nat (=) mul 1. Qed.
Global Instance : Comm_Monoid nat (=) mul 1. Qed.
Global Instance : Semiring nat. Qed.

Global Instance : Assoc (=) min := Nat.min_assoc.
Global Instance : Comm (=) min := Nat.min_comm.
Global Instance : LeftAbsorb (=) 0 min := Nat.min_0_l.
Global Instance : RightAbsorb (=) 0 min := Nat.min_0_r.
Global Instance : LeftDistr (=) add min. lift_distr Nat.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add min. lift_distr Nat.add_min_distr_r. Qed.

End Natural.

(*** Arithmetic of binary numbers. *)
Section Positive.

Global Instance : Equiv N := eq.
Global Instance : Zero N := 0%N.
Global Instance : One N := 1%N.
Global Instance : Min N := N.min.
Global Instance : Add N := N.add.
Global Instance : Mul N := N.mul.

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

Global Instance : Monoid N (=) add 0. Qed.
Global Instance : Comm_Monoid N (=) add 0. Qed.
Global Instance : Monoid N (=) mul 1. Qed.
Global Instance : Comm_Monoid N (=) mul 1. Qed.
Global Instance : Semiring N. Qed.

Global Instance : Assoc (=) min := N.min_assoc.
Global Instance : Comm (=) min := N.min_comm.
Global Instance : LeftAbsorb (=) 0 min := N.min_0_l.
Global Instance : RightAbsorb (=) 0 min := N.min_0_r.
Global Instance : LeftDistr (=) add min. lift_distr N.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add min. lift_distr N.add_min_distr_r. Qed.

End Positive.

(*** Arithmetic of minimum and addition. *)
(* Tropical is a reference to the climate of Brazil, where Imre Simon lived. *)
(* Imre Simon (1943-2009) founded the topic of tropical mathematics. *)
Section Tropical.

Variable X : Type.
Context `{Equiv X, Equivalence X (≡)}.
Context `{Min X, Add X, Zero X, Monoid X (≡) add 0}.
Context `{Assoc X (≡) min, Comm X X (≡) min}.
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

Local Ltac prove := repeat intros []; cbn; try done; f_equal; auto.

Global Instance : Equivalence (≡).
Proof. split; prove. apply Equivalence_Transitive. Qed.

Global Instance : Assoc (≡) add. prove. Qed.
Global Instance : LeftId (≡) 0 add. prove. Qed.
Global Instance : RightId (≡) 0 add. prove. Qed.
Global Instance : Comm (≡) add. prove. Qed.
Global Instance : Assoc (≡) mul. prove. Qed.
Global Instance : LeftId (≡) 1 mul. prove. Qed.
Global Instance : RightId (≡) 1 mul. prove. Qed.
Global Instance : LeftAbsorb (≡) 0 mul. prove. Qed.
Global Instance : RightAbsorb (≡) 0 mul. prove. Qed.
Global Instance : LeftDistr (≡) mul add. prove. Qed.
Global Instance : RightDistr (≡) mul add. prove. Qed.

Global Instance : Monoid trop (≡) add 0. Qed.
Global Instance : Comm_Monoid trop (≡) add 0. Qed.
Global Instance : Monoid trop (≡) mul 1. Qed.
Global Instance : Semiring trop. Qed.
Global Instance : Star_Semiring trop. split; prove. Qed.

End Tropical.

Arguments Tropical {_}.
Arguments Infinity {_}.
