From stars Require Import definitions.

Notation mat X m n := (vec (vec X n) m).
Notation "v @ i" := (vector_lookup_total _ _ i v)
  (left associativity, at level 25, format "v @ i").

Section Polymorphic.

Fixpoint vseq (n : nat) : vec (fin n) n :=
  match n with O => [# ] | S m => Fin.F1 ::: vmap FS (vseq m) end.

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
induction i; simpl. done.
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
simpl; intros; [done|apply IHi].
Qed.

End Polymorphic.

Section Vector.

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

Lemma vec_add_lookup u v i : (u + v)@i = u@i + v@i.
Proof. apply lookup_vzip_with. Qed.

Lemma vec_zero_lookup i : 0@i = 0.
Proof. apply vlookup_replicate. Qed.

Global Instance : Comm_Monoid vec (≡) add 0.
Proof.
repeat split.
intros a b Hab u v Huv i; rewrite ?vec_add_lookup, (Hab i), (Huv i); done.
all: repeat intros ?; rewrite ?vec_add_lookup, ?vec_zero_lookup.
apply assoc; c. apply left_id; c. apply right_id; c. apply comm; c.
Qed.

End Vector.

Section Matrix_multiplication.

Context `{Semiring X}.

Notation "`[ n ]`" := (vec_to_list (vseq n)) (format "`[ n ]`").

Definition mat_dot {m n p} (a : mat X m n) (b : mat X n p) i j : X :=
  Σ ((λ k, a@i@k * b@k@j) <$> `[n]`).

Definition mat_mul {m n p} (a : mat X m n) (b : mat X n p) : mat X m p :=
  mat_build (mat_dot a b).

Notation "a × b" := (mat_mul a b) (at level 50).

Variable m n p q : nat.
Variable a : mat X m n.
Variable b : mat X n p.
Variable c : mat X p q.

Lemma mat_mul_assoc0 i j :
  (a×(b×c))@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
unfold mat_mul; rewrite lookup_mat_build; unfold mat_dot at 1.
erewrite list_fmap_ext with (g:=λ l, a@i@l * mat_dot b c l j).
2: intros k; rewrite lookup_mat_build; done. 2: reflexivity.
Admitted.

Lemma mat_mul_assoc1 i j :
  ((a×b)×c)@i@j ≡ Σ ((λ k, Σ ((λ l, a@i@l * b@l@k * c@k@j)<$>`[n]`))<$>`[p]`).
Proof.
Admitted.

Theorem mat_mul_assoc :
  a × (b × c) ≡ (a × b) × c.
Proof.
intros i j; rewrite mat_mul_assoc0, mat_mul_assoc1; done.
Qed.

End Matrix_multiplication.

Section Square_matrix.

Variable X : Type.
Variable n : nat.
Notation mat := (mat X n n).

Implicit Types a b c : mat.
Implicit Types i j k : fin n.

Context `{Star_Semiring X}.

Global Instance : One mat := mat_build (λ i j, if i =? j then 1 else 0).
Global Instance : Mul mat := mat_mul.

(* The Gauss-Jordan-Floyd-Warshall-Kleene algorithm. *)
Definition mat_plus (m : mat) : mat :=
  let step k m i j := m@i@j + m@i@k * m@k@k{*} * m@k@j in
  foldr (λ k m, mat_build (step k m)) m (vseq n).

Global Instance : Star mat :=
  λ m, 1 + mat_plus m.

Global Instance : @Assoc mat (≡) mul.
Proof. intros a b c; apply mat_mul_assoc; done. Qed.

Global Instance : @LeftId mat (≡) 1 mul. Admitted.
Global Instance : @RightId mat (≡) 1 mul. Admitted.
Global Instance : @LeftAbsorb mat (≡) 0 mul. Admitted.
Global Instance : @RightAbsorb mat (≡) 0 mul. Admitted.
Global Instance : @LeftDistr mat (≡) mul add. Admitted.
Global Instance : @RightDistr mat (≡) mul add. Admitted.

Global Instance : Star_Semiring mat.
Proof. repeat split; try c. Admitted.

Definition mat_transpose (m : mat) : mat :=
  mat_build (λ i j, m@j@i).

End Square_matrix.

Arguments mat_transpose {_ _}.
