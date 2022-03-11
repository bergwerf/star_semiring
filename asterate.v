From stars Require Import definitions matrix.

Section Matrix_asterate.

Variable X : Type.
Variable n : nat.
Notation mat := (mat X n n).

Context `{SR : Star_Semiring X}.

Definition mat_plus (a : mat) : mat :=
  let step k c i j := c@i@j + c@i@k * c@k@k{*} * c@k@j in
  foldr (λ k b, mat_build (step k b)) a (vseq n).

Global Instance : Star mat :=
  λ m, 1 + mat_plus m.

Global Instance : Star_Semiring mat.
Proof. split. c. Admitted.

End Matrix_asterate.
