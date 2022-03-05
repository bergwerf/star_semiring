From stars Require Import definitions.

Notation mat X m n := (vec (vec X m) n).
Notation "v @ i" := (vector_lookup_total _ _ i v)
  (left associativity, at level 25, format "v @ i").

Section Vectors.

Fixpoint vseq (n : nat) : vec (fin n) n :=
  match n with O => [# ] | S m => Fin.F1 ::: vmap FS (vseq m) end.

Lemma vec_prod_lookup_elem_of_zip {X Y n} (u : vec X n) (v : vec Y n) i :
  (u@i, v@i) ∈ zip u v.
Proof.
induction i; inv_vec u; inv_vec v; intros; simpl.
apply elem_of_list_here. apply elem_of_list_further, IHi.
Qed.

Section Equivalence.

Variable X : Type.
Variable n : nat.
Notation vec := (vec X n).

Context `{Equiv X, Equivalence X (≡)}.

Global Instance : Equiv vec := Forall2 equiv.

Lemma vec_equiv_spec u v :
  u ≡ v <-> ∀ i, u@i ≡ v@i.
Proof.
split; intros.
- eapply Forall2_Forall, Forall_forall in H1.
  replace (_ ≡ _) with (uncurry equiv (u@i, v@i)) by done.
  apply H1. apply vec_prod_lookup_elem_of_zip.
- 
Admitted.

Global Instance : Equivalence (≡).
Proof. split.
- intros a; apply vec_equiv_spec; done.
- intros a b; rewrite ?vec_equiv_spec; done.
- intros a b c; rewrite ?vec_equiv_spec; intros Ha Hb.
  etransitivity; [apply Ha|apply Hb].
Qed.

End Equivalence.

End Vectors.

Section Matrix_tools.

Definition mat_map {X Y m n} f : mat X m n -> mat Y m n :=
  vmap (vmap f).

Definition mat_zip {X Y Z m n} f : mat X m n -> mat Y m n -> mat Z m n :=
  vzip_with (vzip_with f).

End Matrix_tools.

Section General_matrix.

Variable X : Type.
Variable w h : nat.
Notation mat := (mat X w h).

Implicit Types a b c : mat.
Implicit Types i : fin h.
Implicit Types j : fin w.

End General_matrix.

Section Square_matrix.

Variable X : Type.
Variable n : nat.

Notation mat := (mat X n n).

Implicit Types m : mat.
Implicit Types i j : fin n.

Context `{Star_Semiring X}.

Definition mat_build (f : fin n -> fin n -> X) : mat :=
  vmap (λ i, vmap (f i) (vseq n)) (vseq n).

Definition mat_dot (a b : mat) (i j : fin n) :=
  srsum (vmap (λ k : fin n, a@i@k * b@k@j) (vseq n)).

Global Instance : Zero mat := mat_build (λ _ _, 0).
Global Instance : One mat := mat_build (λ i j, if i =? j then 1 else 0).
Global Instance : Add mat := λ a b, mat_zip add a b.
Global Instance : Mul mat := λ a b, mat_build (mat_dot a b).

(* The Gauss-Jordan-Floyd-Warshall-Kleene algorithm. *)
Definition mat_plus (m : mat) : mat :=
  let step k m i j := m@i@j + m@i@k * m@k@k{*} * m@k@j in
  foldr (λ k m, mat_build (step k m)) m (vseq n).

Global Instance : Star mat :=
  λ m, 1 + mat_plus m.

Global Instance : @Assoc mat (≡) add. Admitted.
Global Instance : @LeftId mat (≡) 0 add. Admitted.
Global Instance : @RightId mat (≡) 0 add. Admitted.
Global Instance : @Comm mat mat (≡) add. Admitted.
Global Instance : @Assoc mat (≡) mul. Admitted.
Global Instance : @LeftId mat (≡) 1 mul. Admitted.
Global Instance : @RightId mat (≡) 1 mul. Admitted.
Global Instance : @LeftAbsorb mat (≡) 0 mul. Admitted.
Global Instance : @RightAbsorb mat (≡) 0 mul. Admitted.
Global Instance : @LeftDistr mat (≡) mul add. Admitted.
Global Instance : @RightDistr mat (≡) mul add. Admitted.

Global Instance : Monoid mat (≡) add 0. Qed.
Global Instance : Comm_Monoid mat (≡) add 0. Qed.
Global Instance : Monoid mat (≡) mul 1. Qed.
Global Instance : Semiring mat. Qed.
Global Instance : Star_Semiring mat. Admitted.

Definition mat_transpose (m : mat) : mat :=
  mat_build (λ i j, m@j@i).

End Square_matrix.

Arguments mat_build {_ _}.
Arguments mat_transpose {_ _}.
