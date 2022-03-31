From Coq Require Export QArith.
From stdpp Require Export base list fin vector.

Class Infinity (X : Type) := infinity : X.
Class Zero (X : Type) := zero : X.
Class One (X : Type) := one : X.
Class Min (X : Type) := min : X -> X -> X.
Class Add (X : Type) := add : X -> X -> X.
Class Mul (X : Type) := mul : X -> X -> X.
Class Star (X : Type) := star : X -> X.

Definition Σ {X} `{Add X, Zero X} : list X -> X := foldr add zero.
Definition Π {X} `{Mul X, One X} : list X -> X := foldr mul one.

Notation "∞" := (infinity).
Notation "0" := (zero). 
Notation "1" := (one).
Notation "x + y" := (add x y) (left associativity,at level 50).
Notation "x * y" := (mul x y) (left associativity,at level 40).
Notation "x '{*}'":= (star x) (left associativity,at level 31,format "x '{*}'").
Notation "a ⪯ b" := (a + b ≡ b) (at level 70).

Class LeftDistr {X} (R : relation X) (f g : X -> X -> X) :=
  left_distr a x y : R (f a (g x y)) (g (f a x) (f a y)).

Class RightDistr {X} (R : relation X) (f g : X -> X -> X) :=
  right_distr x y a : R (f (g x y) a) (g (f x a) (f y a)).

Class LeftCancel {X} (R : relation X) (f : X -> X -> X) :=
  left_cancel a x y : R (f a x) (f a y) -> R x y.

Class RightCancel {X} (R : relation X) (f : X -> X -> X) :=
  right_cancel x y a : R (f x a) (f y a) -> R x y.

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

Ltac convert_nat_bool_once :=
  match goal with
  | [H : _ =? _ = true |- _]   => apply Nat.eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply Nat.eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply Nat.leb_le in H
  | [H : _ <=? _ = false |- _] => apply Nat.leb_gt in H
  | [H : _ <? _ = true |- _]   => apply Nat.ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply Nat.ltb_ge in H
  | |- (_ =? _ = true)   => apply Nat.eqb_eq
  | |- (_ =? _ = false)  => apply Nat.eqb_neq
  | |- (_ <=? _ = true)  => apply Nat.leb_le
  | |- (_ <=? _ = false) => apply Nat.leb_gt
  | |- (_ <? _ = true)   => apply Nat.ltb_lt
  | |- (_ <? _ = false)  => apply Nat.ltb_ge
  | _ => idtac
  end.

Ltac c := typeclasses eauto.
Ltac split_proper := apply Semigroup_Proper.
Ltac cancel_l := split_proper; [reflexivity|].
Ltac cancel_r := split_proper; [|reflexivity].
Ltac convert_bool := repeat convert_nat_bool_once.

Section Lemmas.

Context `{SR : Semiring X}.

Implicit Types x y : X.
Implicit Types xs : list X.

Lemma left_distr_Σ xs y :
  y * Σ xs ≡ Σ ((λ x, y * x) <$> xs).
Proof.
induction xs; cbn. apply right_absorb; c.
etrans. apply left_distr. rewrite IHxs; done.
Qed.

Lemma right_distr_Σ xs y :
  Σ xs * y ≡ Σ ((λ x, x * y) <$> xs).
Proof.
induction xs; cbn. apply left_absorb; c.
etrans. apply right_distr. rewrite IHxs; done.
Qed.

Lemma equiv_Σ xs ys :
  Forall2 (≡) xs ys -> Σ xs ≡ Σ ys.
Proof.
revert ys; induction xs; intros ys Heq; inversion_clear Heq; cbn.
done. rewrite H, IHxs; done.
Qed.

Lemma equiv_Σ_0 xs :
  Forall (equiv 0) xs -> Σ xs ≡ 0.
Proof.
induction xs; cbn. done.
intros; decompose_Forall_hyps.
rewrite <-H, IHxs. apply left_id; c. done.
Qed.

Lemma equiv_Σ_append xs ys :
  Σ (xs ++ ys) ≡ Σ xs + Σ ys.
Proof.
induction xs; cbn. symmetry; apply left_id; c.
rewrite IHxs; apply assoc; c.
Qed.

Lemma equiv_Σ_fmap {I} f g is :
  (∀ i : I, i ∈ is -> f i ≡ g i) -> Σ (f <$> is) ≡ Σ (g <$> is).
Proof.
intros; apply equiv_Σ, Forall2_fmap, Forall_Forall2_diag, Forall_forall.
intros i Hi; apply H, Hi.
Qed.

Lemma equiv_Σ_zip_with_add xs ys :
  length xs = length ys ->
  Σ xs + Σ ys ≡ Σ (zip_with add xs ys).
Proof.
revert ys; induction xs; intros [|y ys]; cbn; intros; try done.
apply left_id; c. rewrite (assoc _ _ y), <-(assoc _ a), (comm _ _ y).
rewrite assoc, <-(assoc _ (a + y)), IHxs. done. apply Nat.succ_inj, H. c.
Qed.

Lemma Σ_swap_index {I J} (f : I -> J -> X) is js :
  Σ ((λ i, Σ ((λ j, f i j) <$> js)) <$> is) ≡
  Σ ((λ j, Σ ((λ i, f i j) <$> is)) <$> js).
Proof.
revert js; induction is; cbn; intros.
- symmetry; apply equiv_Σ_0.
  apply Forall_forall; intros x Hx.
  apply elem_of_list_fmap in Hx as (_ & -> & _); done.
- rewrite IHis, equiv_Σ_zip_with_add.
  2: rewrite ?fmap_length; done.
  apply equiv_Σ; induction js; cbn. done.
  apply Forall2_cons; done.
Qed.

Lemma Σ_indicator {I} (δ : I -> bool) (f : I -> X) j is :
  (∀ i, δ i = true <-> j = i) -> NoDup is -> j ∈ is ->
  Σ ((λ i, if δ i then f i else 0) <$> is) ≡ f j.
Proof.
induction is as [|i is]; intros Hδ Hdup Hin; cbn.
apply elem_of_nil in Hin; done.
apply NoDup_cons in Hdup as (H1 & H2).
apply elem_of_cons in Hin as [].
- apply Hδ in H as Hδi; subst; rewrite Hδi, equiv_Σ_0.
  apply right_id; c. apply Forall_forall; intros x Hx.
  apply elem_of_list_fmap in Hx as (k & -> & Hk); destruct (δ k) eqn:E.
  apply Hδ in E; subst; done. done.
- rewrite IHis; try done. destruct (δ i) eqn:E.
  apply Hδ in E; subst; done. apply left_id; c.
Qed.

End Lemmas.
