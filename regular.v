From stars Require Import definitions.

Inductive re {X} :=
  | RE_None
  | RE_Empty
  | RE_Literal (x : X)
  | RE_Or (a b : re)
  | RE_Seq (a b : re)
  | RE_Star (a : re).

Notation "a ∣ b" := (RE_Or a b) (at level 52, format "a ∣ b").
Notation "a ⋅ b" := (RE_Seq a b) (at level 51, format "a ⋅ b").
Notation "a ∗" := (RE_Star a) (left associativity, at level 50, format "a ∗").

Section Regular_Expressions.

Variable X : Type.
Notation re := (@re X).

Fixpoint re_in (w : list X) (a : re) :=
  match a with
  | RE_None => False
  | RE_Empty => w = []
  | RE_Literal x => w = [x]
  | RE_Or b c => re_in w b \/ re_in w c
  | RE_Seq b c => ∃ u v, w = u ++ v /\ re_in u b /\ re_in v c
  | RE_Star b => w = [] \/ ∃ vs, w = concat vs /\ Forall (λ v, re_in v b) vs
  end.

Global Instance : Zero re := RE_None.
Global Instance : One re := RE_Empty.
Global Instance : Empty re := RE_None.
Global Instance : ElemOf (list X) re := re_in.
Global Instance : Equiv re := λ a b, ∀ w, w ∈ a <-> w ∈ b.

Global Instance : Add re :=
  λ a b, match a, b with
  | RE_None, _ => b
  | _, RE_None => a
  | RE_Empty, RE_Empty => RE_Empty
  | RE_Empty, RE_Star _ => b
  | RE_Star _, RE_Empty => a
  | _, _ => RE_Or a b
  end.

Global Instance : Mul re :=
  λ a b, match a with
  | RE_None => RE_None
  | RE_Empty => b
  | _ => match b with
    | RE_None => RE_None
    | RE_Empty => a
    | _ => RE_Seq a b
    end
  end.

Global Instance : Star re :=
  λ a, match a with
  | RE_None => RE_Empty
  | RE_Empty => RE_Empty
  | RE_Star _ => a
  | _ => RE_Star a
  end.

Global Instance : @Equivalence re (≡).
Proof. firstorder. Qed.

Lemma re_seq_0_l a : 0⋅a ≡ 0.
Proof. firstorder. Qed.

Lemma re_seq_0_r a : a⋅0 ≡ 0.
Proof. firstorder. Qed.

Lemma re_seq_1_l a :
  1⋅a ≡ a.
Proof.
intros w; cbn; split.
intros (u&v&->&->&Hv); done.
intros Hw; exists [], w; done.
Qed.

Lemma re_seq_1_r a :
  a⋅1 ≡ a.
Proof.
intros w; cbn; split.
intros (u&v&->&Hu&->); simplify_list_eq; done.
intros Hw; exists w, []; simplify_list_eq; done.
Qed.

Lemma re_star_0 :
  0∗ ≡ 1.
Proof.
intros w; cbn; firstorder; subst.
destruct x; decompose_Forall; done.
Qed.

Lemma re_star_1 :
  1∗ ≡ 1.
Proof.
intros w; cbn; firstorder; subst.
apply concat_nil_Forall; done.
Qed.

Lemma re_star_star a :
  a∗∗ ≡ a∗.
Proof.
intros w; cbn; split; intros [H|(vs&->&H)]; auto.
- induction vs as [|v vs]. left; done. decompose_Forall.
  apply IHvs in H0 as [->|(vs'&->&Hvs')]; clear IHvs.
  + simplify_list_eq; firstorder.
  + right; destruct H as [->|(us&->&Hus)]; cbn.
    exists vs'; done. exists (us ++ vs'); split.
    symmetry; apply concat_app. decompose_Forall; done.
- right; exists vs; split; [done|]. eapply Forall_impl.
  apply H. cbn; intros v Hv; right; exists [v]; split.
  cbn; simplify_list_eq; done. decompose_Forall; done.
Qed.

Lemma re_star_expand_left a :
  a∗ ≡ 1∣a⋅a∗.
Proof.
intros w; cbn; split; intros H.
+ destruct H as [->|(vs&->&H)]; [left; done|].
  destruct vs as [|v vs]; [left; done|right]; exists v, (concat vs).
  decompose_Forall; repeat split; try done. right; exists vs; done.
+ destruct H as [->|(u&v&->&Hu&H)]; [left; done|right].
  destruct H as [->|(vs&->&Hvs)]; [exists [u]|exists (u :: vs)];
  cbn; repeat split; decompose_Forall; done.
Qed.

Lemma re_star_expand_right a :
  a∗ ≡ 1∣a∗⋅a.
Proof.
intros w; cbn; split; intros H.
+ destruct H as [->|(vs&->&H)]; [left; done|].
  destruct vs as [|v vs _] using rev_ind; [left; done|right].
  decompose_Forall; exists (concat vs), v; repeat split.
  rewrite concat_app; simplify_list_eq; done.
  right; exists vs; done. done.
+ destruct H as [->|(u&v&->&H&Hv)]; [left; done|right].
  destruct H as [->|(us&->&Hus)]; [exists [v]|exists (us ++ [v])];
  cbn; repeat split; simplify_list_eq; decompose_Forall; try done.
  rewrite concat_app; simplify_list_eq; done.
Qed.

Lemma equiv_re_add a b :
  a + b ≡ a∣b.
Proof.
destruct a, b; cbn; try firstorder.
Qed.

Lemma equiv_re_mul a b :
  a * b ≡ a⋅b.
Proof.
destruct a, b; cbn; try reflexivity; symmetry.
all: try apply re_seq_0_l; try apply re_seq_0_r.
all: try apply re_seq_1_l; try apply re_seq_1_r.
Qed.

Lemma equiv_re_star a :
  a{*} ≡ a∗.
Proof.
destruct a; cbn; try reflexivity; symmetry.
apply re_star_0. apply re_star_1. apply re_star_star.
Qed.

Global Instance : Proper ((≡) ==> (≡) ==> (≡)) RE_Or.
Proof. firstorder. Qed.

Global Instance : Proper ((≡) ==> (≡) ==> (≡)) RE_Seq.
Proof. firstorder. Qed.

Global Instance : Proper ((≡) ==> (≡)) RE_Star.
Proof.
intros a b Hab w; cbn; split; intros [->|(vs&->&H)]; try (left; done); right;
exists vs; split; try done; eapply Forall_impl; try apply H; apply Hab.
Qed.

Global Instance : Proper ((≡) ==> (≡) ==> (≡)) (@add re _).
Proof. intros a b Hab c d Hcd; rewrite ?equiv_re_add, Hab, Hcd; done. Qed.

Global Instance : Proper ((≡) ==> (≡) ==> (≡)) (@mul re _).
Proof. intros a b Hab c d Hcd; rewrite ?equiv_re_mul, Hab, Hcd; done. Qed.

Global Instance : Proper ((≡) ==> (≡)) (@star re _).
Proof. intros a b Hab; rewrite ?equiv_re_star, Hab; done. Qed.

Local Ltac expand := rewrite ?equiv_re_add, ?equiv_re_mul, ?equiv_re_star.

Global Instance : Kleene_Algebra re.
Proof.
split. split. split. c. split. 1,3: split. 1,4: split. 1,3: c.
- intros a b c; expand; firstorder.
- intros a b c; expand; intros w; cbn; split; intros (u&v&->&H).
  + destruct H as (Ha&v1&v2&->&Hv1&Hv2).
    exists (u ++ v1), v2; repeat split; try done.
    apply app_assoc. exists u, v1; done.
  + destruct H as ((u1&u2&->&Hu1&Hu2)&Hv).
    exists u1, (u2 ++ v); repeat split; try done.
    symmetry; apply app_assoc. exists u2, v; done.
- intros a; expand; firstorder.
- intros a; expand; firstorder.
- intros a; expand; apply re_seq_1_l.
- intros a; expand; apply re_seq_1_r.
- intros a b; expand; firstorder.
- intros a b c; expand; firstorder.
- intros a b c; expand; firstorder.
- intros a; expand; apply re_seq_0_l.
- intros a; expand; apply re_seq_0_r.
- intros a; expand; apply re_star_expand_left.
- intros a; expand; apply re_star_expand_right.
- intros a; expand; firstorder.
- intros a b; expand; intros H w; cbn; split; [|auto].
  intros [(u&v&->&[->|(us&->&Hus)]&Hv)|Hw]; simplify_list_eq; try done.
  induction us as [|u us]; simplify_list_eq. done. decompose_Forall.
  apply H; cbn; left; eexists; eexists; auto.
- intros a b; expand; intros H w; cbn; split; [|auto].
  intros [(u&v&->&Hu&[->|(vs&->&Hvs)])|Hw]; simplify_list_eq; try done.
  induction vs as [|v vs] using rev_ind; simplify_list_eq. done.
  rewrite concat_app; simplify_list_eq; rewrite app_assoc.
  decompose_Forall; apply H; cbn; left; eexists; eexists; auto.
Qed.

End Regular_Expressions.
