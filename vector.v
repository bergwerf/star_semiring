From stars Require Import definitions.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.
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

Lemma vlookup_unfold {X k} (u : vec X k) i : u@i = u !!! i.
Proof. done. Qed.

Lemma vlookup_vseq {k} i :
  vseq k !!! i = i.
Proof.
induction i; cbn. done.
rewrite vlookup_map, IHi; done.
Qed.

Lemma vec_ext {X} (a b : vec X n) :
  (∀ i, a@i = b@i) -> a = b.
Proof.
revert b; induction a; intros; inv_vec b; intros. done.
assert (H0 := H 0%fin); cbn in H0; subst. f_equal; apply IHa; intros i.
assert (HS := H (FS i)); cbn in HS; done.
Qed.

Section Vector_append.

Lemma fin_to_nat_eq (i j : fin n) :
  fin_to_nat i = fin_to_nat j -> i = j.
Proof.
revert j; induction i; cbn; intros; inv_fin j; intros; try done.
cbn in H; apply eq_add_S, IHi in H; subst; done.
Qed.

Lemma fin_sum_sig (i : fin (m + n)) :
  { i_m : fin m | i < m /\ @eq nat i i_m } +
  { i_n : fin n | i ≥ m /\ Nat.add m i_n = i }.
Proof.
destruct (lt_dec i m) as [H|H]; [left|right].
- exists (nat_to_fin H); split.
  done. symmetry; apply fin_to_nat_to_fin.
- apply Nat.nlt_ge in H.
  assert (Hi := fin_to_nat_lt i).
  assert (Hi' : i - m < n) by lia.
  exists (nat_to_fin Hi'); split.
  done. rewrite fin_to_nat_to_fin; lia.
Qed.

Definition fin_sum (i : fin (m + n)) :=
  match fin_sum_sig i with
  | inl (exist _ i' _) => inl i'
  | inr (exist _ i' _) => inr i'
  end.

Lemma vlookup_vapp {X} (u : vec X m) (v : vec X n) (i : fin (m + n)) :
  (u +++ v) !!! i = match fin_sum i with
  | inl i' => u !!! i'
  | inr i' => v !!! i'
  end.
Proof.
unfold fin_sum; destruct (fin_sum_sig i) as [Hi|Hi]; destruct Hi as (i'&Hi&Hi').
- induction u; cbn. lia. inv_fin i; inv_fin i'; cbn; intros; try done.
  apply IHu. apply lt_S_n, Hi. apply eq_add_S, Hi'.
- induction u; cbn in *. apply fin_to_nat_eq in Hi'; subst; done.
  inv_fin i; cbn; intros. done. apply IHu; lia.
Qed.

End Vector_append.

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
