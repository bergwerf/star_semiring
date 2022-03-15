From stars Require Import definitions.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.
Notation "v @ i" := (vector_lookup_total _ _ i v)
  (left associativity, at level 25, format "v @ i").

Section Vector_utilities.

Section Vector_indices.

Fixpoint vseq (n : nat) : vec (fin n) n :=
  match n with O => [# ] | S m => Fin.F1 ::: vmap FS (vseq m) end.

Lemma elem_of_vseq n (i : fin n) :
  i ∈ vec_to_list (vseq n).
Proof.
induction n; cbn; inv_fin i; intros.
apply elem_of_list_here. apply elem_of_list_further.
rewrite vec_to_list_map; apply elem_of_list_fmap_1, IHn.
Qed.

Lemma NoDup_vseq n :
  NoDup (vseq n).
Proof.
induction n; cbn. apply NoDup_nil; done.
rewrite vec_to_list_map; apply NoDup_cons; split.
- intros H; apply elem_of_list_fmap in H as (i & H & _); done.
- apply NoDup_fmap. intros i j H; apply Fin.FS_inj, H. apply IHn.
Qed.

Lemma vmap_vseq_add {X m n} (f : fin (m + n) -> X) :
  vmap f (vseq (m + n)) =
  vmap (f ∘ Fin.L n) (vseq m) +++ vmap (f ∘ Fin.R m) (vseq n).
Proof.
unfold compose; induction m; cbn. done. f_equal.
rewrite Vector.map_map, IHm, Vector.map_map; done.
Qed.

End Vector_indices.

Section Vector_lookups.

Context {m n : nat}.

Implicit Types i : fin m.
Implicit Types j : fin n.

Lemma vlookup_unfold {X} (u : vec X m) i : u@i = u !!! i.
Proof. done. Qed.

Lemma vlookup_vseq i :
  vseq m !!! i = i.
Proof.
induction i; cbn. done.
rewrite vlookup_map, IHi; done.
Qed.

Lemma vec_ext {X} (a b : vec X m) :
  (∀ i, a@i = b@i) -> a = b.
Proof.
revert b; induction a; intros; inv_vec b; intros. done.
assert (H0 := H 0%fin); cbn in H0; subst. f_equal; apply IHa; intros i.
assert (HS := H (FS i)); cbn in HS; done.
Qed.

Section Vector_append.

Implicit Types k : fin (m + n).

Lemma fin_sum_sig k :
  { i : fin m | k < m /\ @eq nat k i } +
  { j : fin n | k ≥ m /\ (m + j)%nat = k }.
Proof.
destruct (lt_dec k m) as [H|H]; [left|right].
- exists (nat_to_fin H); split.
  done. symmetry; apply fin_to_nat_to_fin.
- apply Nat.nlt_ge in H.
  assert (Hk := fin_to_nat_lt k).
  assert (Hi : k - m < n) by lia.
  exists (nat_to_fin Hi); split.
  done. rewrite fin_to_nat_to_fin; lia.
Qed.

Definition fin_sum k :=
  match fin_sum_sig k with
  | inl (exist _ i _) => inl i
  | inr (exist _ j _) => inr j
  end.

Local Ltac destruct_fin_sum := unfold fin_sum;
  destruct (fin_sum_sig _) as [(i'&Hlt&Heq)|(j'&Hge&Heq)].

Lemma fin_to_nat_L i : fin_to_nat (Fin.L n i) = fin_to_nat i.
Proof. induction i; cbn; congruence. Qed.

Lemma fin_to_nat_R j : fin_to_nat (Fin.R m j) = (m + fin_to_nat j)%nat.
Proof. induction m; cbn; congruence. Qed.

Lemma fin_sum_L i :
  fin_sum (Fin.L _ i) = inl i.
Proof.
destruct_fin_sum.
- rewrite fin_to_nat_L in Heq; apply fin_to_nat_inj in Heq; subst; done.
- rewrite fin_to_nat_L in Hge; assert(Hi := fin_to_nat_lt i); lia.
Qed.

Lemma fin_sum_R j :
  fin_sum (Fin.R _ j) = inr j.
Proof.
destruct_fin_sum.
- rewrite fin_to_nat_R in Hlt; lia.
- rewrite fin_to_nat_R in Heq; apply Nat.add_cancel_l in Heq.
  apply fin_to_nat_inj in Heq; subst; done.
Qed.

Lemma vlookup_vapp {X} (u : vec X m) (v : vec X n) k :
  (u +++ v) !!! k = match fin_sum k with
  | inl i => u !!! i
  | inr j => v !!! j
  end.
Proof.
destruct_fin_sum.
- induction u; cbn in *. lia. inv_fin k; inv_fin i'; cbn; intros; try done.
  apply IHu. apply lt_S_n, Hlt. apply eq_add_S, Heq.
- induction u; cbn in *. apply fin_to_nat_inj in Heq; subst; done.
  inv_fin k; cbn; intros. done. apply IHu; lia.
Qed.

End Vector_append.

End Vector_lookups.

End Vector_utilities.

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

Lemma vlookup_add u v i : (u + v)@i = u@i + v@i.
Proof. apply vlookup_zip_with. Qed.

Lemma vlookup_zero i : 0@i = 0.
Proof. apply vlookup_replicate. Qed.

Global Instance : Comm_Monoid vec (≡) add 0.
Proof.
repeat split.
intros a b Hab u v Huv i; rewrite ?vlookup_add, (Hab i), (Huv i); done.
all: repeat intros ?; rewrite ?vlookup_add, ?vlookup_zero.
apply assoc; c. apply left_id; c. apply right_id; c. apply comm; c.
Qed.

Context `{IdemP X (≡) add}.

Global Instance : @IdemP vec (≡) add.
Proof.
intros v i; rewrite vlookup_add; done.
Qed.

End Vector_addition.
