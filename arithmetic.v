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

Global Instance : Kleene_Algebra bool.
Proof. repeat split; repeat intros []; cbn; done. Qed.

End Boolean.

(*** Arithmetic of Peano numbers. *)
Section Natural.

Global Instance : Equiv nat := eq.
Global Instance : Zero nat := 0%nat.
Global Instance : One nat := 1%nat.
Global Instance : Join nat := Nat.max.
Global Instance : Meet nat := Nat.min.
Global Instance : Add nat := Nat.add.
Global Instance : Mul nat := Nat.mul.

Global Instance : Assoc (=) max := Nat.max_assoc.
Global Instance : Assoc (=) min := Nat.min_assoc.
Global Instance : Assoc (=) add := Nat.add_assoc.
Global Instance : Assoc (=) mul := Nat.mul_assoc.

Global Instance : Comm (=) max := Nat.max_comm.
Global Instance : Comm (=) min := Nat.min_comm.
Global Instance : Comm (=) add := Nat.add_comm.
Global Instance : Comm (=) mul := Nat.mul_comm.

Global Instance : IdemP (=) max := Nat.max_id.
Global Instance : IdemP (=) min := Nat.min_id.
Global Instance : Absorb (=) max min := Nat.min_max_absorption.
Global Instance : Absorb (=) min max := Nat.max_min_absorption.

Global Instance : LeftId (=) 0 max := Nat.max_0_l.
Global Instance : RightId (=) 0 max := Nat.max_0_r.
Global Instance : LeftId (=) 0 add := Nat.add_0_l.
Global Instance : RightId (=) 0 add := Nat.add_0_r.
Global Instance : LeftId (=) 1 mul := Nat.mul_1_l.
Global Instance : RightId (=) 1 mul := Nat.mul_1_r.

Global Instance : LeftAbsorb (=) 0 min := Nat.min_0_l.
Global Instance : RightAbsorb (=) 0 min := Nat.min_0_r.
Global Instance : LeftAbsorb (=) 0 mul := Nat.mul_0_l.
Global Instance : RightAbsorb (=) 0 mul := Nat.mul_0_r.

Global Instance : LeftDistr (=) mul add := Nat.mul_add_distr_l.
Global Instance : RightDistr (=) mul add := Nat.mul_add_distr_r.
Global Instance : LeftDistr (=) add min. lift_distr Nat.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add min. lift_distr Nat.add_min_distr_r. Qed.
Global Instance : LeftDistr (=) add min. lift_distr Nat.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add min. lift_distr Nat.add_min_distr_r. Qed.

Global Instance : Lattice nat. auto_resolve. Qed.
Global Instance : Semiring nat. auto_resolve. Qed.

End Natural.

(*** Arithmetic of binary numbers. *)
Section Positive.

Global Instance : Equiv N := eq.
Global Instance : Zero N := 0%N.
Global Instance : One N := 1%N.
Global Instance : Join N := N.max.
Global Instance : Meet N := N.min.
Global Instance : Add N := N.add.
Global Instance : Mul N := N.mul.

Global Instance : Assoc (=) join := N.max_assoc.
Global Instance : Assoc (=) meet := N.min_assoc.
Global Instance : Assoc (=) add := N.add_assoc.
Global Instance : Assoc (=) mul := N.mul_assoc.

Global Instance : Comm (=) join := N.max_comm.
Global Instance : Comm (=) meet := N.min_comm.
Global Instance : Comm (=) add := N.add_comm.
Global Instance : Comm (=) mul := N.mul_comm.

Global Instance : IdemP (=) join := N.max_id.
Global Instance : IdemP (=) meet := N.min_id.
Global Instance : Absorb (=) join meet := N.min_max_absorption.
Global Instance : Absorb (=) meet join := N.max_min_absorption.

Global Instance : LeftId (=) 0 join := N.max_0_l.
Global Instance : RightId (=) 0 join := N.max_0_r.
Global Instance : LeftId (=) 0 add := N.add_0_l.
Global Instance : RightId (=) 0 add := N.add_0_r.
Global Instance : LeftId (=) 1 mul := N.mul_1_l.
Global Instance : RightId (=) 1 mul := N.mul_1_r.

Global Instance : LeftAbsorb (=) 0 meet := N.min_0_l.
Global Instance : RightAbsorb (=) 0 meet := N.min_0_r.
Global Instance : LeftAbsorb (=) 0 mul := N.mul_0_l.
Global Instance : RightAbsorb (=) 0 mul := N.mul_0_r.

Global Instance : LeftDistr (=) mul add := N.mul_add_distr_l.
Global Instance : RightDistr (=) mul add := N.mul_add_distr_r.
Global Instance : LeftDistr (=) add meet. lift_distr N.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add meet. lift_distr N.add_min_distr_r. Qed.
Global Instance : LeftDistr (=) add meet. lift_distr N.add_min_distr_l. Qed.
Global Instance : RightDistr (=) add meet. lift_distr N.add_min_distr_r. Qed.

Global Instance : Lattice N. auto_resolve. Qed.
Global Instance : Semiring N. auto_resolve. Qed.

End Positive.

(*** Arithmetic of rational numbers. *)
Section Rational.

Coercion inject_Z : Z >-> Q.

Global Instance : Equiv Q := Qeq.
Global Instance : Zero Q := 0%Z.
Global Instance : One Q := 1%Z.
Global Instance : Add Q := Qplus.
Global Instance : Mul Q := Qmult.

Global Instance : RelDecision Qeq := Qeq_dec.
Global Instance : Assoc (≡) add := Qplus_assoc.
Global Instance : Assoc (≡) mul := Qmult_assoc.
Global Instance : Comm (≡) add := Qplus_comm.
Global Instance : Comm (≡) mul := Qmult_comm.
Global Instance : LeftId (≡) 0 add := Qplus_0_l.
Global Instance : RightId (≡) 0 add := Qplus_0_r.
Global Instance : LeftId (≡) 1 mul := Qmult_1_l.
Global Instance : RightId (≡) 1 mul := Qmult_1_r.
Global Instance : LeftAbsorb (≡) 0 mul := Qmult_0_l.
Global Instance : RightAbsorb (≡) 0 mul := Qmult_0_r.
Global Instance : LeftDistr (≡) mul add := Qmult_plus_distr_r.
Global Instance : RightDistr (≡) mul add := Qmult_plus_distr_l.
Global Instance : Semiring Q. auto_resolve. Qed.

End Rational.

(*** Arithmetic of minimum and addition. *)
(* Tropical is a reference to the climate of Brazil, where Imre Simon lived. *)
(* Imre Simon (1943-2009) founded the topic of tropical mathematics. *)
Section Tropical.

Variable X : Type.
Context `{Equiv X, Equivalence X (≡), Meet X, Add X, Zero X}.
Context `{Semilattice X (≡) meet, Monoid X (≡) add 0}.
Context `{LeftAbsorb X (≡) 0 meet, RightAbsorb X (≡) 0 meet}.
Context `{LeftDistr X (≡) add meet, RightDistr X (≡) add meet}.

Inductive trop := Tropical (x : X) | TInfinity.

Global Instance : Equiv trop := λ a b,
  match a, b with
  | Tropical x, Tropical y => x ≡ y
  | TInfinity, TInfinity => True
  | _, _ => False
  end.

Global Instance : Infinity trop := TInfinity.
Global Instance : Zero trop := TInfinity.
Global Instance : One trop := Tropical 0.

Global Instance : Add trop :=
  λ a b, match a, b with
  | TInfinity, _ => b
  | _, TInfinity => a
  | Tropical x, Tropical y => Tropical (x ∧ y)
  end.

Global Instance : Mul trop :=
  λ a b, match a, b with
  | TInfinity, _ => TInfinity
  | _, TInfinity => TInfinity
  | Tropical x, Tropical y => Tropical (x + y)
  end.

Global Instance trop_star : Star trop :=
  λ _, 1.

Global Instance : Kleene_Algebra trop.
Proof.
repeat split.
4,9: intros [] [] A [] [] B; cbn in *; try done; rewrite A, B; done.
all: repeat intros []; cbn; try done; f_equal. apply Equivalence_Transitive.
apply (assoc meet). apply (comm meet). apply (assoc add).
apply (left_id 0 add). apply (right_id 0 add). apply (idemp meet).
1,2: rewrite (left_id 0 add); intros; apply (idemp meet).
1,2: rewrite (right_id 0 add); intros; apply (idemp meet).
Qed.

End Tropical.

Arguments Tropical {_}.
Arguments TInfinity {_}.

(*** One-point compactification of the rational numbers. *)
Section Compact.

Inductive frac :=
  | Frac (q : Q)
  | Inf.

Coercion Frac : Q >-> frac.

Global Instance : Equiv frac := λ x y,
  match x, y with
  | Frac p, Frac q => p == q
  | Inf, Inf => True
  | _, _ => False
  end.

Global Instance : Infinity frac := Inf.
Global Instance : Zero frac := 0%Z.
Global Instance : One frac := 1%Z.

Global Instance : Add frac := λ x y,
  match x, y with
  | Inf, _ => Inf
  | _, Inf => Inf
  | Frac p, Frac q => Qred (p + q)
  end.

Global Instance : Mul frac := λ x y,
  match x, y with
  | Frac (Qmake Z0 _), _ => 0
  | _, Frac (Qmake Z0 _) => 0
  | Inf, _ => Inf
  | _, Inf => Inf
  | Frac p, Frac q => Qred (p * q)
  end.

Global Instance : Star frac := λ x,
  match x with
  | Frac ((Qmake (Zpos m) n) as p) =>
    if Pos.eqb m n then Inf else Qred (Qinv (1 - p))
  | Frac p => Qred (Qinv (1 - p))
  | Inf => Inf
  end.

Global Instance : Equivalence (≡).
Proof.
split.
- intros []; done.
- intros [] [] H; done.
- intros [] [] [] H H'; try done; cbn; trans q0; done.
Qed.

Global Instance : RelDecision (≡).
Proof.
intros [p|] [q|]. apply (decide (p ≡ q)).
1,2: right; intro H; done. left; done.
Qed.

Local Ltac intro_Q := let i := fresh "i" in intros [[[] i]|].
Local Ltac intros_Q := repeat (intro_Q || let H := fresh "H" in intro H).
Local Ltac reduce_Q := cbn in *; try done; rewrite ?Qred_correct.

Lemma frac_add_hom p q : Frac (p + q) ≡ Frac p + Frac q.
Proof. cbn; rewrite Qred_correct. done. Qed.

Lemma frac_mul_hom p q : Frac (p * q) ≡ Frac p * Frac q.
Proof. destruct p as [[] i], q as [[] j]; reduce_Q; unfold Qeq; done. Qed.

Global Instance : Proper ((≡) ==> (≡)) Frac.
Proof. intros p q H; done. Qed.

Global Instance : Proper ((≡) ==> (≡) ==> (≡)) add.
Proof. intros [] [] H1 [] [] H2; reduce_Q; apply Qplus_comp; done. Qed.

Global Instance : Proper ((≡) ==> (≡) ==> (≡)) mul.
Proof. intros_Q; reduce_Q; apply Qmult_comp; done. Qed.

Global Instance : Proper ((≡) ==> (≡)) star.
Proof.
intros_Q; reduce_Q; try (rewrite H; done).
destruct (p =? i)%positive eqn:E.
- apply Pos.eqb_eq in E; subst. unfold Qeq in H; cbn in H.
  rewrite Z.mul_comm in H; apply Z.mul_cancel_r, Zpos_eq_iff in H; subst.
  rewrite Pos.eqb_refl; done. done.
- apply Pos.eqb_neq in E; destruct (p0 =? i0)%positive eqn:E0.
  apply Pos.eqb_eq in E0; subst. unfold Qeq in H; cbn in H.
  rewrite Z.mul_comm in H; apply Z.mul_cancel_l, Zpos_eq_iff in H; subst; done.
  cbn; rewrite H; done.
Qed.

Local Ltac lift_Qplus H := repeat intros []; reduce_Q; apply H.
Local Ltac lift_Qmult H := intros_Q; reduce_Q; apply H.

Global Instance : Assoc (≡) add. lift_Qplus Qplus_assoc. Qed.
Global Instance : Assoc (≡) mul. Admitted.
Global Instance : Comm (≡) add. lift_Qplus Qplus_comm. Qed.
Global Instance : Comm (≡) mul. lift_Qmult Qmult_comm. Qed.
Global Instance : LeftId (≡) 0 add. lift_Qplus Qplus_0_l. Qed.
Global Instance : RightId (≡) 0 add. lift_Qplus Qplus_0_r. Qed.
Global Instance : LeftId (≡) 1 mul. lift_Qmult Qmult_1_l. Qed.
Global Instance : RightId (≡) 1 mul. lift_Qmult Qmult_1_r. Qed.
Global Instance : LeftAbsorb (≡) 0 mul. lift_Qmult Qmult_0_l. Qed.
Global Instance : RightAbsorb (≡) 0 mul. lift_Qmult Qmult_0_r. Qed.
Global Instance : LeftDistr (≡) mul add. Admitted.
Global Instance : RightDistr (≡) mul add. Admitted.

Lemma star_frac_neq_1 q :
  Frac q ≢ 1 -> (Frac q){*} ≡ /(1 - q).
Proof.
destruct q as [[] i]; intros; reduce_Q; try done.
destruct (p =? i)%positive eqn:E. 2: apply Qred_correct.
exfalso; apply H; apply Pos.eqb_eq in E; subst.
unfold Qeq; cbn; apply Z.mul_comm.
Qed.

Lemma expand_star_frac q :
  / (1 - q) ≡ 1 + q * / (1 - q).
Proof.
Admitted.

Global Instance : Star_Semiring frac.
Proof.
repeat split; try c.
all: intros []. 2,4: done.
all: destruct (decide (Frac q ≡ 1)) as [->|Hq]. 1,3: done.
all: rewrite (star_frac_neq_1 _ Hq). 2: rewrite (comm mul).
all: rewrite expand_star_frac at 1; rewrite frac_add_hom, frac_mul_hom; done.
Qed.

End Compact.
