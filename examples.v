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
Notation "∞" := (Infinity).

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
