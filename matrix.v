From stars Require Import definitions vector.

Notation mat X m n := (vec (vec X n) m).

Section Matrix_utilities.

Context {X : Type}.
Context {m n : nat}.

Definition mat_map {Y} (f : X -> Y) : mat X m n -> mat Y m n :=
  vmap (vmap f).

Definition mat_build (f : fin m -> fin n -> X) : mat X m n :=
  vmap (λ i, vmap (f i) (vseq n)) (vseq m).

Lemma vlookup_mat_build (f : fin m -> fin n -> X) i j :
  (mat_build f)@i@j = f i j.
Proof.
unfold mat_build; rewrite ?vlookup_unfold,
?vlookup_map, ?vlookup_vseq; done.
Qed.

End Matrix_utilities.

Section Matrix_transposition.

Definition mat_transpose {X m n} (a : mat X m n) : mat X n m :=
  mat_build (λ i j, a@j@i).

Theorem mat_transpose_id {X m n} (a : mat X m n) :
  mat_transpose (mat_transpose a) = a.
Proof.
apply vec_ext; intros i; apply vec_ext; intros j.
unfold mat_transpose; rewrite ?vlookup_mat_build; done.
Qed.

End Matrix_transposition.

Section Matrix_multiplication.

Context `{SR : Semiring X}.

Definition mat_dot {m n p} (a : mat X m n) (b : mat X n p) i j : X :=
  Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).

Definition mat_mul {m n p} (a : mat X m n) (b : mat X n p) : mat X m p :=
  mat_build (mat_dot a b).

Notation "a × b" := (mat_mul a b) (at level 40).

Lemma vlookup_mat_mul {m n p} (a : mat X m n) (b : mat X n p) i j :
  (a × b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof.
unfold mat_mul; rewrite vlookup_mat_build; done.
Qed.

Section Proper.

Theorem proper_mat_mul {m n p} (a b : mat X m n) (c d : mat X n p) :
  a ≡ b -> c ≡ d -> a × c ≡ b × d.
Proof.
intros Ha Hc i k; rewrite ?vlookup_mat_mul.
apply equiv_Σ_fmap; intros j _; rewrite (Ha i j), (Hc j k); done.
Qed.

End Proper.

Section Associativity.

Variable m n p q : nat.
Variable a : mat X m n.
Variable b : mat X n p.
Variable c : mat X p q.

Implicit Types k : fin p.
Implicit Types l : fin n.

Lemma assoc_mat_mul_l i j :
  ((a×b)×c)@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
rewrite vlookup_mat_mul. erewrite list_fmap_ext;
[|intros k; rewrite vlookup_mat_mul; done|reflexivity].
apply equiv_Σ_fmap; intros k _. etrans; [apply right_distr_Σ|].
rewrite <-list_fmap_compose; done.
Qed.

Lemma assoc_mat_mul_r i j :
  (a×(b×c))@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
rewrite vlookup_mat_mul. erewrite list_fmap_ext;
[|intros k; rewrite vlookup_mat_mul; done|reflexivity].
etrans. apply equiv_Σ_fmap; intros l _. etrans. apply left_distr_Σ.
rewrite <-list_fmap_compose; unfold compose. apply equiv_Σ_fmap; intros k _.
2: apply Σ_swap_index. apply assoc; c.
Qed.

Theorem assoc_mat_mul :
  a × (b × c) ≡ (a × b) × c.
Proof.
intros i j; rewrite assoc_mat_mul_l, assoc_mat_mul_r; done.
Qed.

End Associativity.

Section Absorption.

Theorem left_absorb_mat_mul {m n p} (a : mat X n p) :
  @mat_mul m n p 0 a ≡ 0.
Proof.
intros i k; rewrite vlookup_mat_mul, ?vlookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?vlookup_zero; symmetry; apply left_absorb; c.
Qed.

Theorem right_absorb_mat_mul {m n p} (a : mat X m n) :
  @mat_mul m n p a 0 ≡ 0.
Proof.
intros i k; rewrite vlookup_mat_mul, ?vlookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?vlookup_zero; symmetry; apply right_absorb; c.
Qed.

End Absorption.

End Matrix_multiplication.

Notation "a × b" := (mat_mul a b) (at level 40).

Section Matrix_semiring.

Variable X : Type.
Variable n : nat.
Notation mat := (mat X n n).

Implicit Types i j k : fin n.

Context `{SR : Semiring X}.

Global Instance : One mat := mat_build (λ i j, if i =? j then 1 else 0).
Global Instance : Mul mat := mat_mul.

Lemma vlookup_one i j : 1@i@j = if i =? j then 1 else 0.
Proof. apply vlookup_mat_build. Qed.

Lemma vlookup_mul a b i j : (a * b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof. apply vlookup_mat_mul. Qed.

Lemma Σ_eqb_indicator (x : X) j :
  j < n -> Σ ((λ i, if i =? j then x else 0) <$> `[n]`) ≡ x.
Proof.
intros; eapply Σ_indicator with (f:=λ _, x)(j:=j).
intros; split; intros Heq. apply Nat.eqb_eq, fin_to_nat_inj in Heq; done.
rewrite Heq; apply Nat.eqb_refl. apply NoDup_vseq. apply elem_of_vseq.
Qed.

Lemma zip_with_fmap {U V W Y} (f : V -> W -> Y) (us : list U) g h :
  zip_with f (g <$> us) (h <$> us) = (λ x, f (g x) (h x)) <$> us.
Proof.
induction us; cbn. done.
f_equal; apply IHus.
Qed.

Global Instance : @LeftId mat (≡) 1 mul.
Proof.
intros a i j; erewrite vlookup_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=i), fin_to_nat_lt.
intros k _; rewrite vlookup_one, Nat.eqb_sym; destruct (k =? i) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply left_id; c. apply left_absorb; c.
Qed.

Global Instance : @RightId mat (≡) 1 mul.
Proof.
intros a i j; erewrite vlookup_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=j), fin_to_nat_lt.
intros k _; rewrite vlookup_one; destruct (k =? j) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply right_id; c. apply right_absorb; c.
Qed.

Global Instance : @LeftDistr mat (≡) mul add.
Proof.
intros a b c i j; rewrite ?vlookup_add, ?vlookup_mul, Σ_zip_with_add.
rewrite zip_with_fmap; apply equiv_Σ_fmap; intros k _.
rewrite ?vlookup_add; apply left_distr.
rewrite ?fmap_length; done.
Qed.

Global Instance : @RightDistr mat (≡) mul add.
Proof.
intros a b c i j; rewrite ?vlookup_add, ?vlookup_mul, Σ_zip_with_add.
rewrite zip_with_fmap; apply equiv_Σ_fmap; intros k _.
rewrite ?vlookup_add; apply right_distr.
rewrite ?fmap_length; done.
Qed.

Global Instance : Semiring mat.
Proof.
repeat split; try c.
intros a b Hab c d Hcd; apply proper_mat_mul; done.
intros a b c; apply assoc_mat_mul.
intros a; apply left_absorb_mat_mul.
intros a; apply right_absorb_mat_mul.
Qed.

End Matrix_semiring.

Section Matrix_blocks.

Context `{SR : Semiring X}.
Notation mat m n := (mat X m n).

Definition blocks {m n p q}
  (a : mat m p) (b : mat m q)
  (c : mat n p) (d : mat n q) : mat (m + n) (p + q) :=
  vzip_with vapp a b +++ vzip_with vapp c d.

Lemma vlookup_blocks {m n p q} a b c d (i : fin (m + n)) (j : fin (p + q)) :
  (blocks a b c d)@i@j =
  match fin_sum i, fin_sum j with
  | inl i', inl j' => a@i'@j'
  | inl i', inr j' => b@i'@j'
  | inr i', inl j' => c@i'@j'
  | inr i', inr j' => d@i'@j'
  end.
Proof.
unfold blocks; rewrite ?vlookup_unfold, vlookup_vapp; destruct (fin_sum i);
rewrite vlookup_zip_with, vlookup_vapp; destruct (fin_sum j); done.
Qed.

Theorem add_blocks {m n p q}
  (a a' : mat m p) (b b' : mat m q)
  (c c' : mat n p) (d d' : mat n q) :
  blocks a b c d + blocks a' b' c' d' ≡
  blocks (a + a') (b + b') (c + c') (d + d').
Proof.
intros i j; rewrite ?vlookup_add, ?vlookup_blocks.
destruct (fin_sum i), (fin_sum j); rewrite ?vlookup_add; done.
Qed.

Lemma Σ_fin_sum {m n p q} (a : mat m (p + q)) (b : mat (p + q) n) i j :
  Σ ((λ k : fin (p + q), a@i@k * b@k@j) <$> `[p + q]`) ≡
  Σ ((λ k : fin p, let l := (Fin.L q k) in a@i@l * b@l@j) <$> `[p]`) +
  Σ ((λ k : fin q, let l := (Fin.R p k) in a@i@l * b@l@j) <$> `[q]`).
Proof.
Admitted.

Theorem mul_blocks {m n p q}
  (a : mat m p) (b : mat m q)
  (c : mat n p) (d : mat n q)
  (e : mat p m) (f : mat p n)
  (g : mat q m) (h : mat q n) :
  blocks a b c d × blocks e f g h ≡ blocks
  (a × e + b × g) (a × f + b × h)
  (c × e + d × g) (c × f + d × h).
Proof.
intros i j; rewrite vlookup_blocks, vlookup_mat_mul, Σ_fin_sum.
destruct (fin_sum i) as [i'|i'] eqn:Hi, (fin_sum j) as [j'|j'] eqn:Hj.
all: rewrite ?vlookup_add, ?vlookup_mat_mul; split_proper.
all: apply equiv_Σ_fmap; intros k _; cbn; rewrite ?vlookup_blocks, Hi, Hj.
all: rewrite ?fin_sum_L, ?fin_sum_R; reflexivity.
Qed.

End Matrix_blocks.
