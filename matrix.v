From stars Require Import definitions vector.

Notation mat X m n := (vec (vec X n) m).
Notation "`[ n ]`" := (vec_to_list (vseq n)) (format "`[ n ]`").

Section Matrix_utilities.

Context {X : Type}.
Context {m n : nat}.

Definition mat_map {Y} (f : X -> Y) : mat X m n -> mat Y m n :=
  vmap (vmap f).

Definition mat_build (f : fin m -> fin n -> X) : mat X m n :=
  vmap (λ i, vmap (f i) (vseq n)) (vseq m).

Lemma lookup_mat_build (f : fin m -> fin n -> X) i j :
  (mat_build f)@i@j = f i j.
Proof.
unfold mat_build; rewrite ?lookup_unfold,
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
unfold mat_transpose; rewrite ?lookup_mat_build; done.
Qed.

End Matrix_transposition.

Section Matrix_multiplication.

Context `{SR : Semiring X}.
Notation mat m n := (mat X m n).

Definition mat_dot {m n p} (a : mat m n) (b : mat n p) i j : X :=
  Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).

Definition mat_mul {m n p} (a : mat m n) (b : mat n p) : mat m p :=
  mat_build (mat_dot a b).

Definition mat_one {n} :=
  mat_build (λ i j : fin n, if i =? j then 1 else 0).

Notation "a × b" := (mat_mul a b) (at level 40).

Lemma lookup_mat_mul {m n p} (a : mat m n) (b : mat n p) i j :
  (a × b)@i@j = Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).
Proof.
unfold mat_mul; rewrite lookup_mat_build; done.
Qed.

Section Proper.

Global Instance proper_mat_mul m n p :
  Proper ((≡) ==> (≡) ==> (≡)) (@mat_mul m n p).
Proof.
intros a b Hab c d Hcd i k; rewrite ?lookup_mat_mul.
apply equiv_Σ_fmap; intros j _; rewrite (Hab i j), (Hcd j k); done.
Qed.

End Proper.

Section Absorption.

Theorem left_absorb_mat_mul {m n p} (a : mat n p) :
  @mat_mul m n p 0 a ≡ 0.
Proof.
intros i k; rewrite lookup_mat_mul, ?lookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?lookup_zero; symmetry; apply left_absorb; c.
Qed.

Theorem right_absorb_mat_mul {m n p} (a : mat m n) :
  @mat_mul m n p a 0 ≡ 0.
Proof.
intros i k; rewrite lookup_mat_mul, ?lookup_zero.
apply equiv_Σ_0, Forall_forall; intros x Hx.
apply elem_of_list_fmap in Hx as (j & -> & _).
rewrite ?lookup_zero; symmetry; apply right_absorb; c.
Qed.

End Absorption.

Section Identity.

Lemma lookup_mat_one {n} (i j : fin n) : mat_one@i@j = if i =? j then 1 else 0.
Proof. apply lookup_mat_build. Qed.

Lemma Σ_eqb_indicator (x : X) (n : nat) (j : fin n) :
  j < n -> Σ ((λ i : fin n, if i =? j then x else 0) <$> `[n]`) ≡ x.
Proof.
intros; eapply Σ_indicator with (f:=λ _, x)(j:=j).
intros; split; intros Heq. apply Nat.eqb_eq, fin_to_nat_inj in Heq; done.
rewrite Heq; apply Nat.eqb_refl. apply NoDup_vseq. apply elem_of_vseq.
Qed.

Theorem left_id_mat_mul {m n} (a : mat m n) :
  mat_one × a ≡ a.
Proof.
intros i j; erewrite lookup_mat_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=i), fin_to_nat_lt.
intros k _; rewrite lookup_mat_one, Nat.eqb_sym; destruct (k =? i) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply left_id; c. apply left_absorb; c.
Qed.

Theorem right_id_mat_mul {m n} (a : mat m n) :
  a × mat_one ≡ a.
Proof.
intros i j; erewrite lookup_mat_mul, equiv_Σ_fmap.
apply Σ_eqb_indicator with (j:=j), fin_to_nat_lt.
intros k _; rewrite lookup_mat_one; destruct (k =? j) eqn:E.
apply Nat.eqb_eq, fin_to_nat_inj in E; subst k.
apply right_id; c. apply right_absorb; c.
Qed.

End Identity.

Section Associativity.

Variable m n p q : nat.
Variable a : mat m n.
Variable b : mat n p.
Variable c : mat p q.

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

Section Distributivity.

Lemma zip_with_fmap {U V W Y} (f : V -> W -> Y) (us : list U) g h :
  zip_with f (g <$> us) (h <$> us) = (λ x, f (g x) (h x)) <$> us.
Proof.
induction us; cbn. done.
f_equal; apply IHus.
Qed.

Theorem left_distr_mat_mul {m n p} (a : mat m n) (b c : mat n p) :
  a × (b + c) ≡ a × b + a × c.
Proof.
intros i j; rewrite ?lookup_add, ?lookup_mat_mul, equiv_Σ_zip_with_add.
rewrite zip_with_fmap; apply equiv_Σ_fmap; intros k _.
rewrite ?lookup_add; apply left_distr.
rewrite ?fmap_length; done.
Qed.

Theorem right_distr_mat_mul {m n p} (a b : mat m n) (c : mat n p) :
  (a + b) × c ≡ a × c + b × c.
Proof.
intros i j; rewrite ?lookup_add, ?lookup_mat_mul, equiv_Σ_zip_with_add.
rewrite zip_with_fmap; apply equiv_Σ_fmap; intros k _.
rewrite ?lookup_add; apply right_distr.
rewrite ?fmap_length; done.
Qed.

End Distributivity.

End Matrix_multiplication.

Notation "a × b" := (mat_mul a b) (at level 40).

Section Matrix_semiring.

Variable X : Type.
Variable n : nat.
Notation mat := (mat X n n).

Context `{SR : Semiring X}.

Global Instance : One mat := mat_one.
Global Instance : Mul mat := mat_mul.

Lemma mul_mat_unfold a b : a * b = a × b.
Proof. done. Qed.

Lemma mat_one_fold : mat_one = 1.
Proof. done. Qed.

Lemma lookup_one i j : 1@i@j = if i =? j then 1 else 0.
Proof. apply lookup_mat_one. Qed.

Global Instance : Semiring mat.
Proof.
repeat split; try c.
intros a b c; apply assoc_mat_mul.
intros a; apply left_id_mat_mul.
intros a; apply right_id_mat_mul.
intros a b c; apply left_distr_mat_mul.
intros a b c; apply right_distr_mat_mul.
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

Lemma lookup_blocks {m n p q} a b c d (i : fin (m + n)) (j : fin (p + q)) :
  (blocks a b c d)@i@j =
  match fin_sum i, fin_sum j with
  | inl i', inl j' => a@i'@j'
  | inl i', inr j' => b@i'@j'
  | inr i', inl j' => c@i'@j'
  | inr i', inr j' => d@i'@j'
  end.
Proof.
unfold blocks; rewrite ?lookup_unfold, vlookup_vapp; destruct (fin_sum i);
rewrite vlookup_zip_with, vlookup_vapp; destruct (fin_sum j); done.
Qed.

Global Instance proper_blocks m n p q :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (@blocks m n p q).
Proof.
intros a a' Ha b b' Hb c c' Hc d d' Hd i j;
rewrite ?lookup_blocks; destruct (fin_sum i), (fin_sum j).
apply Ha. apply Hb. apply Hc. apply Hd.
Qed.

Theorem eq_zero_blocks {m n p q} :
  0 = @blocks m n p q 0 0 0 0.
Proof.
apply vec_ext; intros i; apply vec_ext; intros j.
rewrite lookup_blocks; destruct (fin_sum i), (fin_sum j);
rewrite ?lookup_zero; done.
Qed.

Theorem eq_one_blocks {m n} :
  1 = @blocks m n m n 1 0 0 1.
Proof.
apply vec_ext; intros i; apply vec_ext; intros j; rewrite lookup_blocks.
unfold fin_sum; destruct (fin_sum_sig i) as [[i' Hi]|[i' Hi]];
destruct (fin_sum_sig j) as [[j' Hj]|[j' Hj]].
all: assert (Hi' := fin_to_nat_lt i'); assert (Hj' := fin_to_nat_lt j').
all: rewrite ?lookup_zero, ?lookup_one; try rewrite <-Hi; try rewrite <-Hj.
- reflexivity.
- replace (i =? m + j') with false; [done|symmetry]; convert_bool; lia.
- replace (m + i' =? j) with false; [done|symmetry]; convert_bool; lia.
- destruct (m + i' =? m + j') eqn:?, (i' =? j') eqn:?;
  convert_bool; try done; lia.
Qed.

Theorem equiv_add_blocks {m n p q}
  (a a' : mat m p) (b b' : mat m q)
  (c c' : mat n p) (d d' : mat n q) :
  blocks a b c d + blocks a' b' c' d' ≡
  blocks (a + a') (b + b') (c + c') (d + d').
Proof.
intros i j; rewrite ?lookup_add, ?lookup_blocks.
destruct (fin_sum i), (fin_sum j); rewrite ?lookup_add; done.
Qed.

Lemma fmap_vseq_add {m n} (f : fin (m + n) -> X) :
  f <$> `[m + n]` = (f ∘ Fin.L n <$> `[m]`) ++ (f ∘ Fin.R m <$> `[n]`).
Proof.
rewrite <-?vec_to_list_map, <-vec_to_list_app.
rewrite vmap_vseq_add; done.
Qed.

Theorem equiv_mul_blocks {m n p q}
  (a : mat m p) (b : mat m q)
  (c : mat n p) (d : mat n q)
  (e : mat p m) (f : mat p n)
  (g : mat q m) (h : mat q n) :
  blocks a b c d × blocks e f g h ≡ blocks
  (a × e + b × g) (a × f + b × h)
  (c × e + d × g) (c × f + d × h).
Proof.
intros i j; rewrite lookup_blocks, lookup_mat_mul.
rewrite fmap_vseq_add, equiv_Σ_append; unfold compose.
destruct (fin_sum i) as [i'|i'] eqn:Hi, (fin_sum j) as [j'|j'] eqn:Hj.
all: rewrite ?lookup_add, ?lookup_mat_mul; split_proper.
all: apply equiv_Σ_fmap; intros k _; cbn; rewrite ?lookup_blocks, Hi, Hj.
all: rewrite ?fin_sum_L, ?fin_sum_R; reflexivity.
Qed.

End Matrix_blocks.
