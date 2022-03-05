*semiring library for Coq
=========================
While the word *library* is in the title, the aim of this project is not so much
to create a programming library, as it is to explore the algebra and algorithms
underlying *semirings and Kleene algebras. I was originally motivated to explore
this topic by [1]. A good introduction of the topic can be found in [2]. More
references are collected in `refs.bib`. I use the `stdpp` utility library [3].
The Coq library "Algebraic Tools for Binary Relations" at [4] also contains a
matrix asteration algorithm based on the inductive block construction. An
important difference with the ATBR library is that we use vectors to represent
matrices, while ATBR uses functions.

[1]: http://r6.ca/blog/20110808X035622Z.html
[2]: https://doi.org/10.1016/0304-3975(77)90056-1
[3]: https://gitlab.mpi-sws.org/iris/stdpp
[4]: https://github.com/coq-community/atbr
