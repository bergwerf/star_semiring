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

Lemma vzip_with_lookup {X Y Z} (f : X -> Y -> Z) u v (i : fin n) :
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
Proof. apply vzip_with_lookup. Qed.

Lemma vec_zero_lookup i : 0@i = 0.
Proof. apply vlookup_replicate. Qed.

Ltac prove := repeat intros ?; rewrite ?vec_add_lookup, ?vec_zero_lookup; done.

Global Instance : Assoc (≡) add. prove. Qed.
Global Instance : LeftId (≡) 0 add. prove. Qed.
Global Instance : RightId (≡) 0 add. prove. Qed.
Global Instance : Comm (≡) add. prove. Qed.

Global Instance : Monoid vec (≡) add 0. Qed.
Global Instance : Comm_Monoid vec (≡) add 0. Qed.

End Vector.

Section Matrix_multiplication.

Variable X : Type.

Context `{Add X, Mul X, Zero X}.

Definition mat_dot {m n k} (a : mat X m k) (b : mat X k n) i j : X :=
  srsum (vmap (λ k, a@i@k * b@k@j) (vseq k)).

Definition mat_mul {m n k} (a : mat X m k) (b : mat X k n) : mat X m n :=
  mat_build (mat_dot a b).

End Matrix_multiplication.

Section Square_matrix.

Variable X : Type.
Variable n : nat.
Notation mat := (mat X n n).

Implicit Types a b c : mat.
Implicit Types i j k : fin n.

Context `{Star_Semiring X}.

Global Instance : One mat := mat_build (λ i j, if i =? j then 1 else 0).
Global Instance : Mul mat := mat_mul _.

(* The Gauss-Jordan-Floyd-Warshall-Kleene algorithm. *)
Definition mat_plus (m : mat) : mat :=
  let step k m i j := m@i@j + m@i@k * m@k@k{*} * m@k@j in
  foldr (λ k m, mat_build (step k m)) m (vseq n).

Global Instance : Star mat :=
  λ m, 1 + mat_plus m.

Global Instance : @Assoc mat (≡) mul. Admitted.
Global Instance : @LeftId mat (≡) 1 mul. Admitted.
Global Instance : @RightId mat (≡) 1 mul. Admitted.
Global Instance : @LeftAbsorb mat (≡) 0 mul. Admitted.
Global Instance : @RightAbsorb mat (≡) 0 mul. Admitted.
Global Instance : @LeftDistr mat (≡) mul add. Admitted.
Global Instance : @RightDistr mat (≡) mul add. Admitted.

Global Instance : Monoid mat (≡) mul 1. Qed.
Global Instance : Semiring mat. Qed.
Global Instance : Star_Semiring mat. Admitted.

Definition mat_transpose (m : mat) : mat :=
  mat_build (λ i j, m@j@i).

End Square_matrix.

Arguments mat_transpose {_ _}.
