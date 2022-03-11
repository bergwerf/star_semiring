From stars Require Import definitions.

Notation mat X m n := (vec (vec X n) m).
Notation "v @ i" := (vector_lookup_total _ _ i v)
  (left associativity, at level 25, format "v @ i").

Section Vector_utilities.

Fixpoint vseq (n : nat) : vec (fin n) n :=
  match n with O => [# ] | S m => Fin.F1 ::: vmap FS (vseq m) end.

Lemma NoDup_vseq n :
  NoDup (vseq n).
Proof.
Admitted.

Lemma elem_of_vseq n (i : fin n) :
  i ∈ vec_to_list (vseq n).
Proof.
Admitted.

Context {m n : nat}.

Definition mat_build {X} (f : fin m -> fin n -> X) : mat X m n :=
  vmap (λ i, vmap (f i) (vseq n)) (vseq m).

Definition mat_map {X Y} f : mat X m n -> mat Y m n :=
  vmap (vmap f).

Definition mat_zip {X Y Z} f : mat X m n -> mat Y m n -> mat Z m n :=
  vzip_with (vzip_with f).

Lemma vlookup_conv {X k} (u : vec X k) i : u@i = u !!! i.
Proof. done. Qed.

Lemma vlookup_vseq {k} i :
  vseq k !!! i = i.
Proof.
induction i; cbn. done.
rewrite vlookup_map, IHi; done.
Qed.

Lemma lookup_mat_build {X} (f : fin m -> fin n -> X) i j :
  (mat_build f)@i@j = f i j.
Proof.
unfold mat_build; rewrite ?vlookup_conv,
?vlookup_map, ?vlookup_vseq; done.
Qed.

Lemma lookup_vzip_with {X Y Z} (f : X -> Y -> Z) u v (i : fin n) :
  (vzip_with f u v)@i = f (u@i) (v@i).
Proof.
induction i; inv_vec u; inv_vec v;
cbn; intros; [done|apply IHi].
Qed.

Lemma vec_ext {X} (a b : vec X n) :
  (∀ i, a@i = b@i) -> a = b.
Proof.
revert b; induction a; intros; inv_vec b; intros. done.
assert(H0 := H 0%fin); cbn in H0; subst. f_equal; apply IHa; intros i.
assert(HS := H (FS i)); cbn in HS; done.
Qed.

End Vector_utilities.

Notation "`[ n ]`" := (vec_to_list (vseq n)) (format "`[ n ]`").

Section Vector_addition.

Variable X : Type.
Variable n : nat.
Notation vec := (vec X n).

Context `{Equiv X, Equivalence X (≡)}.

Global Instance : Equiv vec := λ u v, ∀ i, u@i ≡ v@i.

Global Instance : Equivalence (≡).
Proof.
split; repeat intros ?; try done.
transitivity (y@i); done.
Qed.

Context `{Add X, Zero X, Comm_Monoid _ (≡) add 0}.

Global Instance : Add vec := vzip_with add.
Global Instance : Zero vec := vreplicate n 0.

Lemma lookup_add u v i : (u + v)@i = u@i + v@i.
Proof. apply lookup_vzip_with. Qed.

Lemma lookup_zero i : 0@i = 0.
Proof. apply vlookup_replicate. Qed.

Global Instance : Comm_Monoid vec (≡) add 0.
Proof.
repeat split.
intros a b Hab u v Huv i; rewrite ?lookup_add, (Hab i), (Huv i); done.
all: repeat intros ?; rewrite ?lookup_add, ?lookup_zero.
apply assoc; c. apply left_id; c. apply right_id; c. apply comm; c.
Qed.

End Vector_addition.

Section Matrix_transposition.

Definition mat_transpose {X m n} (a : mat X m n) : mat X n m :=
  mat_build (λ i j, a@j@i).

Theorem mat_transpose_id {X m n} (a : mat X m n) :
  mat_transpose (mat_transpose a) = a.
Proof.
apply vec_ext; intros i; apply vec_ext; intros j.
unfold mat_transpose; rewrite ?lookup_mat_build; done.
Qed.

End Matrix_transposition.

Section Matrix_multiplication.

Context `{SR : Semiring X}.

Definition mat_dot {m n p} (a : mat X m n) (b : mat X n p) i j : X :=
  Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).

Definition mat_mul {m n p} (a : mat X m n) (b : mat X n p) : mat X m p :=
  mat_build (mat_dot a b).

Notation "a × b" := (mat_mul a b) (at level 50).

Lemma lookup_mat_mul {m n p} (a : mat X m n) (b : mat X n p) i j :
  (a × b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof.
unfold mat_mul; rewrite lookup_mat_build; done.
Qed.

Section Proper.

Theorem mat_mul_proper {m n p} (a b : mat X m n) (c d : mat X n p) :
  a ≡ b -> c ≡ d -> a × c ≡ b × d.
Proof.
intros Ha Hc i k; rewrite ?lookup_mat_mul.
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

Lemma mat_mul_assoc_l i j :
  ((a×b)×c)@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
rewrite lookup_mat_mul. erewrite list_fmap_ext;
[|intros k; rewrite lookup_mat_mul; done|reflexivity].
apply equiv_Σ_fmap; intros k _. etrans; [apply right_distr_Σ|].
rewrite <-list_fmap_compose; done.
Qed.

Lemma mat_mul_assoc_r i j :
  (a×(b×c))@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
rewrite lookup_mat_mul. erewrite list_fmap_ext;
[|intros k; rewrite lookup_mat_mul; done|reflexivity].
etrans. apply equiv_Σ_fmap; intros l _. etrans. apply left_distr_Σ.
rewrite <-list_fmap_compose; unfold compose. apply equiv_Σ_fmap; intros k _.
2: apply Σ_swap_index. apply assoc; c.
Qed.

Theorem mat_mul_assoc :
  a × (b × c) ≡ (a × b) × c.
Proof.
intros i j; rewrite mat_mul_assoc_l, mat_mul_assoc_r; done.
Qed.

End Associativity.

Section Absorption.

Theorem mat_mul_left_absorb {m n p} (a : mat X n p) :
  @mat_mul m n p 0 a ≡ 0.
Proof.
intros i k; rewrite lookup_mat_mul, ?lookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?lookup_zero; symmetry; apply left_absorb; c.
Qed.

Theorem mat_mul_right_absorb {m n p} (a : mat X m n) :
  @mat_mul m n p a 0 ≡ 0.
Proof.
intros i k; rewrite lookup_mat_mul, ?lookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?lookup_zero; symmetry; apply right_absorb; c.
Qed.

End Absorption.

End Matrix_multiplication.

Section Matrix_semiring.

Variable X : Type.
Variable n : nat.
Notation mat := (mat X n n).

Implicit Types i j k : fin n.

Context `{SR : Semiring X}.

Global Instance : One mat := mat_build (λ i j, if i =? j then 1 else 0).
Global Instance : Mul mat := mat_mul.

Lemma lookup_one i j : 1@i@j = if i =? j then 1 else 0.
Proof. apply lookup_mat_build. Qed.

Lemma lookup_mul a b i j : (a * b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof. apply lookup_mat_mul. Qed.

Lemma Σ_eqb_indicator (x : X) j :
  j < n -> Σ ((λ i, if i =? j then x else 0) <$> `[n]`) ≡ x.
Proof.
intros; eapply Σ_indicator with (f:=λ _, x)(j0:=j).
intros; split; intros Heq. apply Nat.eqb_eq, fin_to_nat_inj in Heq; done.
rewrite Heq; apply Nat.eqb_refl. apply NoDup_vseq. apply elem_of_vseq.
Qed.

Global Instance :
  @LeftId mat (≡) 1 mul.
Proof.
intros a i j; erewrite lookup_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=i), fin_to_nat_lt.
intros k _; rewrite lookup_one, Nat.eqb_sym; destruct (k =? i) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply left_id; c. apply left_absorb; c.
Qed.

Global Instance :
  @RightId mat (≡) 1 mul.
Proof.
intros a i j; erewrite lookup_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=j), fin_to_nat_lt.
intros k _; rewrite lookup_one; destruct (k =? j) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply right_id; c. apply right_absorb; c.
Qed.

Global Instance : @LeftDistr mat (≡) mul add. Admitted.
Global Instance : @RightDistr mat (≡) mul add. Admitted.

Global Instance : Semiring mat.
Proof.
repeat split; try c.
intros a b Hab c d Hcd; apply mat_mul_proper; done.
intros a b c; apply mat_mul_assoc.
intros a; apply mat_mul_left_absorb.
intros a; apply mat_mul_right_absorb.
Qed.

End Matrix_semiring.
