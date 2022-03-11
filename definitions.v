From stdpp Require Export base list fin vector.

Class Zero (X : Type) := zero : X.
Class One (X : Type) := one : X.
Class Min (X : Type) := min : X -> X -> X.
Class Add (X : Type) := add : X -> X -> X.
Class Mul (X : Type) := mul : X -> X -> X.
Class Star (X : Type) := star : X -> X.

Definition Σ {X} `{Add X, Zero X} : list X -> X := foldr add zero.
Definition Π {X} `{Mul X, One X} : list X -> X := foldr mul one.

Notation "0" := (zero). 
Notation "1" := (one).
Notation "x + y" := (add x y).
Notation "x * y" := (mul x y).
Notation "x '{*}'" := (star x) (at level 30, format "x '{*}'").
Notation "a ⪯ b" := (a + b ≡ b) (at level 70).

Class LeftDistr {X} (R : relation X) (f g : X -> X -> X) :=
  left_distr a x y : R (f a (g x y)) (g (f a x) (f a y)).

Class RightDistr {X} (R : relation X) (f g : X -> X -> X) :=
  right_distr x y a : R (f (g x y) a) (g (f x a) (f y a)).

Class Semigroup
  (X : Type) (R : relation X) (f : X -> X -> X) : Prop :=
{
  Semigroup_Proper              :> Proper (R ==> R ==> R) f;
  Semigroup_Assoc               :> Assoc R f;
}.

Class Comm_Semigroup
  (X : Type) (R : relation X) (f : X -> X -> X) : Prop :=
{
  Comm_Semigroup_Semigroup      :> Semigroup X R f;
  Comm_Semigroup_Comm           :> Comm R f;
}.

Class Monoid
  (X : Type) (R : relation X) (f : X -> X -> X) (unit : X) : Prop :=
{
  Monoid_Semigroup              :> Semigroup X R f;
  Monoid_LeftId                 :> LeftId R unit f;
  Monoid_RightId                :> RightId R unit f;
}.

Class Comm_Monoid
  (X : Type) (R : relation X) (f : X -> X -> X) (unit : X) : Prop :=
{
  Comm_Monoid_Monoid            :> Monoid X R f unit;
  Comm_Monoid_Comm              :> Comm R f;
}.

Class Semiring
  (X : Type)
  `{_equiv : Equiv X, _add : Add X, _mul : Mul X}
  `{_zero : Zero X, _one : One X} : Prop :=
{
  Semiring_Equivalence          :> Equivalence (≡);
  Semiring_Comm_Monoid          :> Comm_Monoid X (≡) add 0;
  Semiring_Monoid               :> Monoid X (≡) mul 1;
  Semiring_LeftDistr            :> @LeftDistr X (≡) mul add;
  Semiring_RightDistr           :> @RightDistr X (≡) mul add;
  Semiring_LeftAbsorb           :> @LeftAbsorb X (≡) 0 mul;
  Semiring_RightAbsorb          :> @RightAbsorb X (≡) 0 mul;
}.

Class Star_Semiring
  (X : Type)
  `{_equiv : Equiv X, _add : Add X, _mul : Mul X, _star : Star X}
  `{_zero : Zero X, _one : One X} : Prop :=
{
  Star_Semiring_Semiring        :> Semiring X;
  left_expand_star x            : x{*} ≡ 1 + x * x{*};
  right_expand_star x           : x{*} ≡ 1 + x{*} * x;
}.

Class Kleene_Algebra
  (X : Type)
  `{_equiv : Equiv X, _add : Add X, _mul : Mul X, _star : Star X}
  `{_zero : Zero X, _one : One X} : Prop :=
{
  Kleene_Algebra_Star_Semiring  :> Star_Semiring X;
  Kleene_Algebra_IdemP          :> @IdemP X (≡) add;
  left_intro_star a x           : a * x ⪯ x -> a{*} * x ⪯ x;
  right_intro_star a x          : x * a ⪯ x -> x * a{*} ⪯ x;
}.

Ltac c := typeclasses eauto.
Ltac split_proper := apply Semigroup_Proper.
Ltac cancel_l := split_proper; [reflexivity|].
Ltac cancel_r := split_proper; [|reflexivity].

Section Lemmas.

Context `{SR : Semiring X}.

Implicit Types x y : X.
Implicit Types xs : list X.

Lemma Σ_left_distr xs y :
  y * Σ xs ≡ Σ ((λ x, y * x) <$> xs).
Proof.
induction xs; simpl. apply right_absorb; c.
etrans. apply left_distr. rewrite IHxs; done.
Qed.

Lemma Σ_right_distr xs y :
  Σ xs * y ≡ Σ ((λ x, x * y) <$> xs).
Proof.
induction xs; simpl. apply left_absorb; c.
etrans. apply right_distr. rewrite IHxs; done.
Qed.

Lemma Σ_equiv xs ys :
  Forall2 (≡) xs ys -> Σ xs ≡ Σ ys.
Proof.
revert ys; induction xs; intros ys Heq; inversion_clear Heq; cbn.
done. rewrite H, IHxs; done.
Qed.

Lemma Σ_swap_index {I J} (f : I -> J -> X) is js :
  Σ ((λ i, Σ ((λ j, f i j) <$> js)) <$> is) ≡
  Σ ((λ j, Σ ((λ i, f i j) <$> is)) <$> js).
Proof.
Admitted.

End Lemmas.
