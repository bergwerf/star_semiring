From stars Require Import definitions vector matrix.

Section Matrix_asterate.

Variable X : Type.
Notation sq n := (mat X n n).
Notation mat m n := (mat X m n).

Context `{SR : Star_Semiring X}.

Section Inductive_construction.

Section Block_construction.

Variable m n : nat.
Variable star_m: sq m -> sq m.
Variable star_n: sq n -> sq n.

Definition mat_star_blocks
  (a : sq m) (b : mat m n)
  (c : mat n m) (d : sq n) : sq (m + n) :=
  let d'     := star_n d     in
  let bd'    := b × d'       in
  let d'c    := d' × c       in
  let f      := a + bd' × c  in
  let f'     := star_m f     in
  let f'bd'  := f' × bd'     in
  let d'cf'  := d'c × f'     in
  blocks f' f'bd' d'cf' (d' + d'cf' × bd').

Hypothesis left_expand_star_m : ∀ a, star_m a ≡ 1 + a * star_m a.
Hypothesis left_expand_star_n : ∀ a, star_n a ≡ 1 + a * star_n a.

Lemma left_expand_mat_star_blocks a b c d :
  mat_star_blocks a b c d ≡ 1 + blocks a b c d * mat_star_blocks a b c d.
Proof.
unfold mat_star_blocks.
rewrite eq_one_blocks, mul_mat_unfold, equiv_mul_blocks, equiv_add_blocks.
remember (a + (b × star_n d) × c) as f; apply proper_blocks.
- rewrite assoc_mat_mul, <-right_distr_mat_mul, assoc_mat_mul, <-Heqf.
  apply left_expand_star_m.
- rewrite left_id, <-?assoc_mat_mul, assoc_mat_mul with (b:=c).
  rewrite left_distr_mat_mul, assoc_mat_mul with (a:=b).
  rewrite (assoc add), comm with (y:=b×_).
  rewrite <-(assoc add), <-right_distr_mat_mul.
  rewrite assoc_mat_mul with (a:=b), <-Heqf, assoc_mat_mul with (a:=f).
  rewrite <-left_id_mat_mul with (a:=b×star_n d) at 2.
  rewrite mat_one_fold, <-right_distr_mat_mul, <-mul_mat_unfold.
  rewrite <-left_expand_star_m; reflexivity. all: c.
- admit.
- admit.
Admitted.

End Block_construction.

Arguments mat_star_blocks {_ _}.

Definition mat_S_partition {n} (a : sq (S n)) :=
  (([# [# vhd (vhd a) ]], [# vtl (vhd a) ]),
  (vmap (λ r, [# vhd r ]) (vtl a), vmap vtl (vtl a))).

Definition mat_star_ind_step {n} star_ind (a : sq (S n)) :=
  let p := mat_S_partition a in
  mat_star_blocks (mat_map star) star_ind p.1.1 p.1.2 p.2.1 p.2.2.

Fixpoint mat_star_ind {n} : sq n -> sq n :=
  match n with
  | 0 => λ x, x
  | S m => mat_star_ind_step mat_star_ind
  end.

Lemma blocks_S_partition {n} (a : sq (S n)) :
  let p := mat_S_partition a in
  a = blocks p.1.1 p.1.2 p.2.1 p.2.2.
Proof.
inv_vec a; intros a0 a. inv_vec a0; intros a00 a01.
apply vec_ext; intros i; apply vec_ext; intros j; inv_fin i; inv_fin j;
cbn; try done; intros; f_equal; rewrite vlookup_zip_with, ?vlookup_map; cbn.
all: rewrite <-Vector.eta; reflexivity.
Qed.

Lemma mat_star_ind_S_unfold {n} (a : sq (S n)) :
  mat_star_ind a = mat_star_ind_step mat_star_ind a.
Proof.
done.
Qed.

Lemma left_expand_mat_star_ind n (a : sq n) :
  mat_star_ind a ≡ 1 + a * mat_star_ind a.
Proof.
induction n. cbn; inv_vec a; done.
rewrite blocks_S_partition with (a:=a) at 2.
rewrite mat_star_ind_S_unfold; unfold mat_star_ind_step.
rewrite left_expand_mat_star_blocks at 1.
done. admit. apply IHn.
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
