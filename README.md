*semiring library for Coq
=========================
While the word *library* is in the title, the aim of this project is not so much
to create a programming library, as it is to explore the algebra and algorithms
underlying *semirings and Kleene algebras. I was originally motivated to explore
this topic by [1]. A good introduction of the topic can be found in [2]. More
references are collected in `REFS.bib`. I use the `stdpp` utility library [3].
The Coq library "Algebraic Tools for Binary Relations" at [4] also contains a
matrix asteration algorithm based on the inductive block construction. An
important difference with the ATBR library is that we use vectors to represent
matrices, while ATBR uses functions.

[1]: https://r6.ca/blog/20110808T035622Z.html
[2]: https://doi.org/10.1016/0304-3975(77)90056-1
[3]: https://gitlab.mpi-sws.org/iris/stdpp
[4]: https://github.com/coq-community/atbr

Compact rationals
-----------------
The one-point compactification of rational numbers as defined in [1] is _not_ a
*semiring since it fails to satisfy the distributive law. Consider the following
counterexample:
```
(1 + -1) * ∞ ≠ 1 * ∞ + -1 * ∞
```
All other laws are satisfied, which is proven in `arithmetic.v`. I do not know a
way to change the definitions such that the distributive law is also satisfied,
except for restricting it to the finite domain.

Matrix inversion
----------------
By implementing two matrix asteration algorithms, the inductive block
construction and the Warshall-Floyd-Kleene algorithm, I discovered that not all
algorithms give rise to a matrix inversion algorithm. Unless I made a mistake,
it turns out that matrix inversion is _not_ a natural consequence of a solution
to the *semering rules. More details are in the `examples.v` file.
