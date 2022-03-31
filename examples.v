From stars Require Import definitions arithmetic regular vector matrix asterate.

(*** This example show how to compute the reflexive transitive closure. *)
Module Ex1.

Example adj : mat bool 5 5 := [#
  [# 0; 1; 0; 0; 0];
  [# 0; 0; 1; 0; 0];
  [# 0; 0; 0; 1; 1];
  [# 0; 1; 0; 0; 0];
  [# 0; 0; 0; 1; 0]].

Example example_connectivity :
  adj{*} = [#
  [# 1; 1; 1; 1; 1];
  [# 0; 1; 1; 1; 1];
  [# 0; 1; 1; 1; 1];
  [# 0; 1; 1; 1; 1];
  [# 0; 1; 1; 1; 1]].
Proof. done. Qed.

End Ex1.

(*** This example show how to convert an ε-NFA to a regular expression. *)
Module Ex2.

Notation "'A'" := (0%fin). Notation "'B'" := (1%fin). Notation "'C'" := (2%fin).
Notation "'D'" := (3%fin). Notation "'E'" := (4%fin).
Notation "i ~ j" := (RE_Literal (i, j)) (at level 30, format "i ~ j").

Definition graph := mat_build
  (λ i j : fin 5, if Ex1.adj@i@j then i ~ j else ∅).

(* The resulting regular expression represents *)
(* _all_ possible paths from node A to node D. *)
Example example_path_re :
  (graph{*})@A@D = A~B⋅((B~C⋅(C~D∣C~E⋅E~D)⋅D~B)∗⋅(B~C⋅(C~D∣C~E⋅E~D))).
Proof. done. Qed.

(* We can _first_ compute regular expressions, and *)
(* then evaluate them in a *semiring such as bool. *)
Example example_re_eval :
  mat_map (re_eval bool) (mat_map (fmap (λ _, true)) graph{*}) = Ex1.adj{*}.
Proof. done. Qed.

End Ex2.

(* This example show how to compute the shortest path length. *)
Module Ex3.

Notation "^ n" := (Tropical n) (at level 30, format "^ n").

Definition edge_delta : mat (trop N) 6 6 := [#
  [# ∞; ^7; ^9;  ∞;  ∞;^14];
  [# ∞;  ∞;^10;^15;  ∞;  ∞];
  [# ∞;  ∞;  ∞;^11;  ∞; ^2];
  [# ∞;  ∞;  ∞;  ∞; ^6;  ∞];
  [# ∞;  ∞;  ∞;  ∞;  ∞; ^9];
  [# ∞;  ∞;  ∞;  ∞;  ∞;  ∞]]%N.

Definition path_delta : mat N 6 6 := [#
  [# 0;  7;  9; 20; 20; 11];
  [# 0;  0; 10; 15; 21; 12];
  [# 0;  0;  0; 11; 11;  2];
  [# 0;  0;  0;  0;  6; 13];
  [# 0;  0;  0;  0;  0;  9];
  [# 0;  0;  0;  0;  0;  0]]%N.

Definition cl_sym {X n} `{Add X} (m : mat X n n) := m + mat_transpose m.

Example example_shortest_paths :
  (cl_sym edge_delta){*} = mat_map Tropical (cl_sym path_delta).
Proof. done. Qed.

End Ex3.

(* This example shows how to invert matrices. *)
Module Ex4.

Notation "⌜ a ⌝" := (mat_map Frac a) (format "⌜ a ⌝").

Section Matrix_inversion.

Context {n : nat}.
Notation mat X := (mat X n n).

Definition frac_neg (x : frac) : frac :=
  match x with
  | Frac p => Qopp p
  | Inf => Inf
  end.

Definition mat_neg (a : mat Q) := mat_map Qopp a.
Definition mat_inv (a : mat Q) : mat frac := ⌜1 + mat_neg a⌝{*}.

Theorem mul_mat_inv_l_1 (a : mat Q) :
  mat_inv a * ⌜a⌝ ≡ 1.
Proof.
unfold mat_inv; remember (1 + mat_neg a) as b.
replace ⌜a⌝ with (1 + ⌜mat_neg b⌝).
rewrite left_distr, (right_id 1 mul).
rewrite left_expand_star at 1; rewrite <-(assoc add).
(* Does this actually hold? It seems not. *)
(* Infinities in ⌜b⌝{*} cannot be cancelled. *)
Abort.

End Matrix_inversion.

Definition matrix_A := mat_map inject_Z [#
  [# 2; 1];
  [# 0; 2]]%Z.

Definition matrix_B := mat_map inject_Z [#
  [# 3; -2;  4];
  [# 1;  0;  2];
  [# 0;  1;  0]]%Z.

Example example_mat_inv_ident :
  mat_inv matrix_A * ⌜matrix_A⌝ ≡ 1.
Proof. done. Qed.

(***
Inversion fails for matrix B!
-----------------------------
But it succeeds when using the Warshall-Floyd-Kleene algorithm `mat_plus_WFK`.
Apparently the result is sensitive to the implementation. This makes it unlikely
that `mat_inv a * ⌜a⌝ ≡ 1` is actually provable. I think the block construction
`mat_star_blocks` uses some 'detours' that introduce ∞ into the matrix. Although
on paper it looks like the Kleene star inherently produces a matrix inverse,
this glances over the conversion from `Q` to `frac`. Without infinity point
there is no Kleene star, and with ∞ there is no matrix inversion. It is
specifically the WFK algorithm that does implement matrix inversion.

In other words: a Kleene star algorithm is not automatically a matrix inversion
algorithm. The inductive block construction `mat_star_ind` is a counterexample.
*)

Example example_mat_inv_fail :
  mat_inv matrix_B ≡ [#
  [# ∞; ∞; ∞];
  [# ∞; ∞; ∞];
  [# ∞; ∞; ∞]].
Proof. done. Qed.

Definition mat_star_WFK `{Star_Semiring X} {n} (a : mat X n n) :=
  1 + mat_plus_WFK X a n.

Definition mat_inv_WFK {n} (a : mat Q n n) :=
  mat_star_WFK ⌜1 + mat_neg a⌝.

Example example_mat_inv_WFK :
  mat_inv_WFK matrix_B ≡
  mat_map Frac [#
    [#    1;   -2;    2];
    [#    0;    0;    1];
    [# -1/2;  3/2;   -1]
  ]%Q.
Proof. done. Qed.

End Ex4.
