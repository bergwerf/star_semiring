From stars Require Import definitions.

Notation "v @ i" := (vector_lookup_total _ _ i v)
  (left associativity, at level 25, format "v @ i").

Fixpoint vseq (n : nat) : vec (fin n) n :=
  match n with
  | O => [# ]
  | S m => Fin.F1 ::: vmap FS (vseq m)
  end.

Section Matrices.

Variable X : Type.
Context `{Star_Semiring X}.

Variable n : nat.
Definition mat := vec (vec X n) n.

Implicit Types m : mat.
Implicit Types i j : fin n.

Definition mat_build (f : fin n -> fin n -> X) : mat :=
  vmap (λ i, vmap (f i) (vseq n)) (vseq n).

Definition mat_dot (a b : mat) (i j : fin n) :=
  srsum (vmap (λ k : fin n, a@i@k * b@k@j) (vseq n)).

Global Instance : Equiv mat :=
  λ a b, Forall2 (Forall2 equiv) (vmap vec_to_list a) (vmap vec_to_list b).

Global Instance : Zero mat := mat_build (λ _ _, 0).
Global Instance : One mat := mat_build (λ i j, if i =? j then 1 else 0).
Global Instance : Add mat := λ a b, vzip_with (vzip_with add) a b.
Global Instance : Mul mat := λ a b, mat_build (mat_dot a b).

(* The Gauss-Jordan-Floyd-Warshall-Kleene algorithm. *)
Definition mat_plus (m : mat) : mat :=
  let step k m i j := m@i@j + m@i@k * m@k@k{*} * m@k@j in
  foldr (λ k m, mat_build (step k m)) m (vseq n).

Global Instance : Star mat :=
  λ m, 1 + mat_plus m.

Global Instance : Equivalence (≡). Admitted.
Global Instance : Assoc (≡) add. Admitted.
Global Instance : LeftId (≡) 0 add. Admitted.
Global Instance : RightId (≡) 0 add. Admitted.
Global Instance : Comm (≡) add. Admitted.
Global Instance : Assoc (≡) mul. Admitted.
Global Instance : LeftId (≡) 1 mul. Admitted.
Global Instance : RightId (≡) 1 mul. Admitted.
Global Instance : LeftAbsorb (≡) 0 mul. Admitted.
Global Instance : RightAbsorb (≡) 0 mul. Admitted.
Global Instance : LeftDistr (≡) mul add. Admitted.
Global Instance : RightDistr (≡) mul add. Admitted.

Global Instance : Monoid mat (≡) add 0. Qed.
Global Instance : Comm_Monoid mat (≡) add 0. Qed.
Global Instance : Monoid mat (≡) mul 1. Qed.
Global Instance : Semiring mat. Qed.
Global Instance : Star_Semiring mat. Admitted.

Definition mat_transpose (m : mat) : mat :=
  mat_build (λ i j, m@j@i).

End Matrices.

Arguments mat_build {_ _}.
Arguments mat_transpose {_ _}.

Section Matrix_tools.

Definition mat_map {X Y n} f : mat X n -> mat Y n :=
  vmap (vmap f).

Definition mat_zip {X Y Z n} f : mat X n -> mat Y n -> mat Z n :=
  vzip_with (vzip_with f).

End Matrix_tools.
