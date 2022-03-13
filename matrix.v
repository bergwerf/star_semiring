From stars Require Import definitions.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.
Notation mat X m n := (vec (vec X n) m).
Notation "v @ i" := (vector_lookup_total _ _ i v)
  (left associativity, at level 25, format "v @ i").

Section Vector_utilities.

Section Vector_indices.

Fixpoint vseq (n : nat) : vec (fin n) n :=
  match n with O => [# ] | S m => Fin.F1 ::: vmap FS (vseq m) end.

Lemma NoDup_vseq n :
  NoDup (vseq n).
Proof.
induction n; cbn. apply NoDup_nil; done.
rewrite vec_to_list_map; apply NoDup_cons; split.
- intros H; apply elem_of_list_fmap in H as (i & H & _); done.
- apply NoDup_fmap. intros i j H; apply Fin.FS_inj, H. apply IHn.
Qed.

Lemma elem_of_vseq n (i : fin n) :
  i ∈ vec_to_list (vseq n).
Proof.
induction n; cbn; inv_fin i; intros.
apply elem_of_list_here. apply elem_of_list_further.
rewrite vec_to_list_map; apply elem_of_list_fmap_1, IHn.
Qed.

End Vector_indices.

Section Vector_lookups.

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

End Vector_lookups.

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

Context `{IdemP X (≡) add}.

Global Instance : @IdemP vec (≡) add.
Proof.
intros v i; rewrite lookup_add; done.
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

Notation "a × b" := (mat_mul a b) (at level 40).

Lemma lookup_mat_mul {m n p} (a : mat X m n) (b : mat X n p) i j :
  (a × b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof.
unfold mat_mul; rewrite lookup_mat_build; done.
Qed.

Section Proper.

Theorem proper_mat_mul {m n p} (a b : mat X m n) (c d : mat X n p) :
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

Lemma assoc_mat_mul_l i j :
  ((a×b)×c)@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
rewrite lookup_mat_mul. erewrite list_fmap_ext;
[|intros k; rewrite lookup_mat_mul; done|reflexivity].
apply equiv_Σ_fmap; intros k _. etrans; [apply right_distr_Σ|].
rewrite <-list_fmap_compose; done.
Qed.

Lemma assoc_mat_mul_r i j :
  (a×(b×c))@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
rewrite lookup_mat_mul. erewrite list_fmap_ext;
[|intros k; rewrite lookup_mat_mul; done|reflexivity].
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
intros i k; rewrite lookup_mat_mul, ?lookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?lookup_zero; symmetry; apply left_absorb; c.
Qed.

Theorem right_absorb_mat_mul {m n p} (a : mat X m n) :
  @mat_mul m n p a 0 ≡ 0.
Proof.
intros i k; rewrite lookup_mat_mul, ?lookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?lookup_zero; symmetry; apply right_absorb; c.
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

Lemma lookup_one i j : 1@i@j = if i =? j then 1 else 0.
Proof. apply lookup_mat_build. Qed.

Lemma lookup_mul a b i j : (a * b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof. apply lookup_mat_mul. Qed.

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
intros a i j; erewrite lookup_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=i), fin_to_nat_lt.
intros k _; rewrite lookup_one, Nat.eqb_sym; destruct (k =? i) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply left_id; c. apply left_absorb; c.
Qed.

Global Instance : @RightId mat (≡) 1 mul.
Proof.
intros a i j; erewrite lookup_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=j), fin_to_nat_lt.
intros k _; rewrite lookup_one; destruct (k =? j) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply right_id; c. apply right_absorb; c.
Qed.

Global Instance : @LeftDistr mat (≡) mul add.
Proof.
intros a b c i j; rewrite ?lookup_add, ?lookup_mul, Σ_zip_with_add.
rewrite zip_with_fmap; apply equiv_Σ_fmap; intros k _.
rewrite ?lookup_add; apply left_distr.
rewrite ?fmap_length; done.
Qed.

Global Instance : @RightDistr mat (≡) mul add.
Proof.
intros a b c i j; rewrite ?lookup_add, ?lookup_mul, Σ_zip_with_add.
rewrite zip_with_fmap; apply equiv_Σ_fmap; intros k _.
rewrite ?lookup_add; apply right_distr.
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

Definition blocks {k l m n}
  (a : mat k m) (b : mat k n)
  (c : mat l m) (d : mat l n) : mat (k + l) (m + n) :=
  vzip_with vapp a b +++ vzip_with vapp c d.

Definition fin_split {m n} : fin (m + n) -> fin m + fin n.
Admitted.

Lemma fin_split_spec {m n} (i : fin (m + n)) :
  match fin_split i with
  | inl j => i < m /\ @eq nat j i
  | inr j => i ≥ m /\ Nat.add m j = i
  end.
Admitted.

Lemma lookup_blocks {k l m n} a b c d
  (i : fin (k + l)) (j : fin (m + n)) (Hi : i < k) (Hj : j < m) :
  (blocks a b c d)@i@j =
  match fin_split i, fin_split j with
  | inl i', inl j' => a@i'@j'
  | inl i', inr j' => b@i'@j'
  | inr i', inl j' => c@i'@j'
  | inr i', inr j' => d@i'@j'
  end.
Proof.
Admitted.

Theorem add_blocks {k l m n}
  (a a' : mat k m) (b b' : mat k n)
  (c c' : mat l m) (d d' : mat l n) :
  blocks a b c d + blocks a' b' c' d' ≡
  blocks (a + a') (b + b') (c + c') (d + d').
Proof.
Admitted.

Theorem mul_blocks {k l m n}
  (a : mat k m) (b : mat k n)
  (c : mat l m) (d : mat l n)
  (e : mat m k) (f : mat m l)
  (g : mat n k) (h : mat n l) :
  blocks a b c d × blocks e f g h ≡ blocks
  (a × e + b × g) (a × f + b × h)
  (c × e + d × g) (c × f + d × h).
Proof.
Admitted.

End Matrix_blocks.
