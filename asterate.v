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

Notation "x '{m*}'":= (star_m x) (at level 31, format "x '{m*}'").
Notation "x '{n*}'":= (star_n x) (at level 31, format "x '{n*}'").

Definition mat_star_blocks
  (a : sq m) (b : mat m n) 
  (c : mat n m) (d : sq n) : sq (m + n) :=
  let d'     := d{n*}        in
  let bd'    := b × d'       in
  let d'c    := d' × c       in
  let f      := a + bd' × c  in
  let f'     := f{m*}        in
  let f'bd'  := f' × bd'     in
  let d'cf'  := d'c × f'     in
  blocks f' f'bd' d'cf' (d' + d'cf' × bd').

Ltac semiring_remove_zero :=
  rewrite ?(left_id 0 add), ?(right_id 0 add);
  rewrite ?(left_absorb 0 mul), ?(right_absorb 0 mul).

Ltac semiring_normalize_add :=
  rewrite ?(assoc add).

Ltac semiring_cycle_add :=
  etrans; [apply (comm add)|semiring_normalize_add].

Ltac semiring_cancel :=
  reflexivity || cancel_r || semiring_cycle_add.

Ltac mat_normalize :=
  rewrite <-?mat_mul_fold;
  rewrite ?left_distr_mat_mul, ?right_distr_mat_mul, ?assoc_mat_mul;
  rewrite ?left_id_mat_mul, ?right_id_mat_mul; semiring_normalize_add.

Section Left_expand.

Hypothesis left_expand_star_m : ∀ a, a{m*} ≡ 1 + a * a{m*}.
Hypothesis left_expand_star_n : ∀ a, a{n*} ≡ 1 + a * a{n*}.

Lemma left_expand_mat_star_blocks a b c d :
  mat_star_blocks a b c d ≡ 1 + blocks a b c d * mat_star_blocks a b c d.
Proof.
unfold mat_star_blocks.
rewrite <-mat_mul_fold, eq_one_blocks, equiv_mul_blocks, equiv_add_blocks.
remember (a + b × d{n*} × c) as f; apply proper_blocks; semiring_remove_zero.
- rewrite left_expand_star_m at 1; rewrite Heqf at 1.
  mat_normalize; do 1 semiring_cancel.
- rewrite left_expand_star_m at 1; rewrite Heqf at 1.
  mat_normalize; do 3 semiring_cancel.
- rewrite left_expand_star_n at 1.
  mat_normalize; do 1 semiring_cancel.
- trans (d{n*} × (1 + c × f{m*} × b × d{n*})).
  mat_normalize; do 1 semiring_cancel.
  rewrite left_expand_star_n at 1.
  mat_normalize; do 5 semiring_cancel.
Qed.

End Left_expand.

Section Right_expand.

Hypothesis right_expand_star_m : ∀ a, a{m*} ≡ 1 + a{m*} * a.
Hypothesis right_expand_star_n : ∀ a, a{n*} ≡ 1 + a{n*} * a.

Lemma right_expand_mat_star_blocks a b c d :
  mat_star_blocks a b c d ≡ 1 + mat_star_blocks a b c d * blocks a b c d.
Proof.
unfold mat_star_blocks.
rewrite <-mat_mul_fold, eq_one_blocks, equiv_mul_blocks, equiv_add_blocks.
remember (a + b × d{n*} × c) as f; apply proper_blocks; semiring_remove_zero.
- rewrite right_expand_star_m at 1; rewrite Heqf at 2.
  mat_normalize; do 1 semiring_cancel.
- rewrite right_expand_star_n at 1.
  mat_normalize; do 1 semiring_cancel.
- rewrite right_expand_star_m at 1; rewrite Heqf at 2.
  mat_normalize; do 3 semiring_cancel.
- trans ((1 + d{n*} × c × f{m*} × b) × d{n*}).
  mat_normalize; do 1 semiring_cancel.
  rewrite right_expand_star_n at 2.
  mat_normalize; do 1 semiring_cancel.
Qed.

End Right_expand.

Section Left_intro.

Hypothesis  left_intro_star_m : ∀ a x, a * x ⪯ x -> a{m*} * x ⪯ x.
Hypothesis  left_intro_star_n : ∀ a x, a * x ⪯ x -> a{n*} * x ⪯ x.

End Left_intro.

Section Right_intro.

Hypothesis  right_intro_star_m : ∀ a x, x * a ⪯ x -> x * a{m*} ⪯ x.
Hypothesis  right_intro_star_n : ∀ a x, x * a ⪯ x -> x * a{n*} ⪯ x.

End Right_intro.

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

Lemma mat_star_ind_S_unfold {n} (a : sq (S n)) :
  mat_star_ind a = mat_star_ind_step mat_star_ind a.
Proof.
done.
Qed.

Lemma blocks_S_partition {n} (a : sq (S n)) :
  let p := mat_S_partition a in
  a = blocks p.1.1 p.1.2 p.2.1 p.2.2.
Proof.
inv_vec a; intros a0 a. inv_vec a0; intros a00 a01.
apply vec_ext; intros i; apply vec_ext; intros j; inv_fin i; inv_fin j;
cbn; try done; intros; f_equal; rewrite vlookup_zip_with, ?vlookup_map; cbn.
all: rewrite <-Vector.eta; reflexivity.
Qed.

Section Mat_map_star.

Ltac inv_fin_1 i := inv_fin i; [|intros i; inv_fin i].

Lemma left_expand_mat_map_star (a : sq 1) :
  mat_map star a ≡ 1 + a * mat_map star a.
Proof.
inv_vec a; intros a; inv_vec a; intros x i j; inv_fin_1 i; inv_fin_1 j; cbn.
rewrite (right_id 0 add); apply left_expand_star.
Qed.

Lemma right_expand_mat_map_star (a : sq 1) :
  mat_map star a ≡ 1 + mat_map star a * a.
Proof.
inv_vec a; intros a; inv_vec a; intros x i j; inv_fin_1 i; inv_fin_1 j; cbn.
rewrite (right_id 0 add); apply right_expand_star.
Qed.

End Mat_map_star.

Lemma left_expand_mat_star_ind n (a : sq n) :
  mat_star_ind a ≡ 1 + a * mat_star_ind a.
Proof.
induction n. cbn; inv_vec a; done.
rewrite blocks_S_partition with (a:=a) at 2.
rewrite mat_star_ind_S_unfold; unfold mat_star_ind_step.
rewrite left_expand_mat_star_blocks at 1; [done|idtac|apply IHn].
apply left_expand_mat_map_star.
Qed.

Lemma right_expand_mat_star_ind n (a : sq n) :
  mat_star_ind a ≡ 1 + mat_star_ind a * a.
Proof.
induction n. cbn; inv_vec a; done.
rewrite blocks_S_partition with (a:=a) at 3.
rewrite mat_star_ind_S_unfold; unfold mat_star_ind_step.
rewrite right_expand_mat_star_blocks at 1; [done|idtac|apply IHn].
apply right_expand_mat_map_star.
Qed.

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
