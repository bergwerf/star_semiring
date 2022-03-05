From stdpp Require Export base list fin vector.

Class Zero (X : Type) := zero : X.
Class One (X : Type) := one : X.
Class Min (X : Type) := min : X -> X -> X.
Class Add (X : Type) := add : X -> X -> X.
Class Mul (X : Type) := mul : X -> X -> X.
Class Star (X : Type) := star : X -> X.

Definition srsum {X} `{Add X, Zero X} : list X -> X := foldr add zero.
Definition srprod {X} `{Mul X, One X} : list X -> X := foldr mul one.

Notation "0" := (zero). 
Notation "1" := (one).
Notation "x + y" := (add x y).
Notation "x * y" := (mul x y).
Notation "x '{*}'" := (star x) (at level 30, format "x '{*}'").
Notation "a ⪯ b" := (a + b ≡ b) (at level 70).

Class LeftDistr {X} (R : relation X) (f g : X -> X -> X) :=
  distr_l a x y : R (f a (g x y)) (g (f a x) (f a y)).

Class RightDistr {X} (R : relation X) (f g : X -> X -> X) :=
  distr_r x y a : R (f (g x y) a) (g (f x a) (f y a)).

Class Monoid (X : Type) (R : relation X) (f : X -> X -> X) (id : X)
  `{Assoc _ R f, LeftId _ R id f, RightId _ R id f}.

Class Comm_Monoid (X : Type) (R : relation X) (f : X -> X -> X) (id : X)
  `{Monoid _ R f id, Comm _ _ R f}.

Class Semiring (X : Type)
  `{Equiv X, Equivalence X (≡)}
  `{Add X, Mul X, Zero X, One X}
  `{Comm_Monoid _ (≡) add 0, Monoid _ (≡) mul 1}
  `{LeftDistr _ (≡) mul add, RightDistr _ (≡) mul add}
  `{LeftAbsorb _ (≡) 0 mul, RightAbsorb _ (≡) 0 mul}.

Class Star_Semiring (X : Type) `{Semiring X, Star X} := {
  star_expand_l x : x{*} ≡ 1 + x * x{*};
  star_expand_r x : x{*} ≡ 1 + x{*} * x;
}.

Class Kleene_Algebra (X : Type) `{Star_Semiring X, IdemP _ (≡) add} := {
  star_intro_l a x : a * x ⪯ x -> a{*} * x ⪯ x;
  star_intro_r a x : x * a ⪯ x -> x * a{*} ⪯ x;
}.
