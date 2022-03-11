From stars Require Import definitions.

Section Regular_Expressions.

Variable X : Type.

Inductive re :=
  | RE_None
  | RE_Empty
  | RE_Literal (x : X)
  | RE_Or (a b : re)
  | RE_Seq (a b : re)
  | RE_Star (a : re).

Fixpoint re_elem_of (w : list X) (a : re) :=
  match a with
  | RE_None => False
  | RE_Empty => w = []
  | RE_Literal x => w = [x]
  | RE_Or b c => re_elem_of w b \/ re_elem_of w c
  | RE_Seq b c => ∃ u v, w = u ++ v /\ re_elem_of u b /\ re_elem_of v c
  | RE_Star b => ∃ u n, w = concat (repeat u n) /\ re_elem_of u b
  end.

Global Instance : Empty re := RE_None.
Global Instance : ElemOf (list X) re := re_elem_of.
Global Instance : Equiv re := λ a b, ∀ w, w ∈ a <-> w ∈ b.
Global Instance : Zero re := RE_None.
Global Instance : One re := RE_Empty.

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
  λ a b, match a, b with
  | RE_None, _ => RE_None
  | _, RE_None => RE_None
  | RE_Empty, _ => b
  | _, RE_Empty => a
  | _, _ => RE_Seq a b
  end.

Global Instance : Star re :=
  λ a, match a with
  | RE_None => RE_Empty
  | RE_Empty => RE_Empty
  | RE_Star _ => a
  | _ => RE_Star a
  end.

Global Instance : Equivalence (≡).
Proof.
split; repeat intros ?; auto.
symmetry; auto. etrans; auto.
Qed.

End Regular_Expressions.

Arguments RE_Literal {_}.
Arguments RE_Or {_}.
Arguments RE_Seq {_}.
Arguments RE_Star {_}.

Notation "'ε'" := (RE_Empty _).
Notation "a ∣ b" := (RE_Or a b) (at level 52, format "a ∣ b").
Notation "a ⋅ b" := (RE_Seq a b) (at level 51, format "a ⋅ b").
Notation "a ∗" := (RE_Star a) (at level 50, format "a ∗").
