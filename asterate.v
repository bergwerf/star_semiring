From stars Require Import definitions vector matrix.

Section Matrix_asterate.

Variable X : Type.
Notation sq n := (mat X n n).
Notation mat m n := (mat X m n).

Context `{SR : Star_Semiring X}.

Section Inductive_construction.

Definition mat_star_ind_step {m n}
  (star_m: sq m -> sq m) (star_n: sq n -> sq n)
  (a : sq m) (b : mat m n) (c : mat n m) (d : sq n) : sq (m + n) :=
  let d'     := star_n d     in
  let bd'    := b × d'       in
  let d'c    := d' × c       in
  let f      := a + bd' × c  in
  let f'     := star_m f     in
  let f'bd'  := f' × bd'     in
  let d'cf'  := d'c × f'     in
  blocks f' f'bd' d'cf' (d' + d'cf' × bd').

Fixpoint mat_star_ind {n} : sq n -> sq n :=
  match n with
  | 0 => λ x, x
  | S m => λ x : mat (S m) (S m),
    let a := [# [# vhd (vhd x) ]] in
    let b := [# vtl (vhd x) ] in
    let c := vmap (λ r, [# vhd r ]) (vtl x) in
    let d := vmap vtl (vtl x) in
    mat_star_ind_step (mat_map star) mat_star_ind a b c d
  end.

Lemma left_expand_mat_star_ind n (a : sq n) :
  mat_star_ind a ≡ 1 + a * mat_star_ind a.
Proof.
Admitted.

Lemma right_expand_mat_star_ind n (a : sq n) :
  mat_star_ind a ≡ 1 + mat_star_ind a * a.
Proof.
Admitted.

Lemma left_intro_mat_star_ind n (a b : sq n) :
  a * b ⪯ b -> mat_star_ind a * b ⪯ b.
Proof.
Admitted.

Lemma right_intro_mat_star_ind n (a b : sq n) :
  b * a ⪯ b -> b * mat_star_ind a ⪯ b.
Proof.
Admitted.

End Inductive_construction.

Section Warshall_Floyd_Kleene.

Definition mat_plus_WFK {n} (a : sq n) : sq n :=
  let step k c i j := c@i@j + c@i@k * c@k@k{*} * c@k@j in
  foldr (λ k b, mat_build (step k b)) a (vseq n).

End Warshall_Floyd_Kleene.

Section Matrix_star_semiring.

Variable n : nat.
Notation mat := (sq n).

Global Instance : Star mat :=
  λ a, 1 + mat_plus_WFK a.

Global Instance : Star_Semiring mat.
Proof. split. c. Admitted.

End Matrix_star_semiring.

End Matrix_asterate.
