Missing APIs from the types we cover (APIs have been added after this formalization was done)

# Cell

* Structural conversion for slices.  The matching operations in our model would be
  `&mut Cell<(A, B)>` -> `&mut (Cell<A>, Cell<B>)` and
  `&Cell<(A, B)>` -> `&(Cell<A>, Cell<B>)` (both being NOPs).

# ZST

* Something like the example from <https://github.com/rust-lang/unsafe-code-guidelines/issues/168#issuecomment-512528361>
