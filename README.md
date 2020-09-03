# LAMBDA-RUST COQ DEVELOPMENT

This is the Coq development accompanying lambda-Rust.

## Prerequisites

This version is known to compile with:

 - Coq 8.12.0
 - A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for
installing the dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update, do `git pull`.  After an update, the development may fail to compile
because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.

## Structure

* The folder [lang](theories/lang) contains the formalization of the lambda-Rust
  core language, including the theorem showing that programs with data races get
  stuck.
* The folder [lifetime](theories/lifetime) proves the rules of the lifetime
  logic, including derived constructions like (non-)atomic persistent borrows.
  * The subfolder [model](theories/lifetime/model) proves the core rules, which
    are then sealed behind a module signature in
    [lifetime.v](theories/lifetime/lifetime.v).
* The folder [typing](theories/typing) defines the domain of semantic types,
  interpretations of all the judgments, as well as proofs of all typing rules.
  * [type.v](theories/typing/type.v) contains the definition of a semantic type.
  * [programs.v](theories/typing/programs.v) defines the typing judgements for
    instructions and function bodies.
  * [soundness.v](theories/typing/soundness.v) contains the main soundness
    theorem of the type system.
  * The subfolder [examples](theories/typing/examples) shows how the examples
    from the technical appendix can be type-checked in Coq.
  * The subfolder [lib](theories/typing/lib) contains proofs of safety of some
    unsafely implement types from the Rust standard library and some user
    crates: `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `RwLock`, `mem::swap`,
    `thread::spawn`, `take_mut::take`, `alias::once` as well as converting `&&T`
    to `&Box<T>`.

## Where to Find the Proof Rules From the Paper

### Type System Rules

The files in [typing](theories/typing) prove semantic versions of the proof
rules given in the paper.  Notice that mutable borrows are called "unique
borrows" in the Coq development.

| Proof Rule            | File            | Lemma                 |
|-----------------------|-----------------|-----------------------|
| T-bor-lft (for shr)   | shr_bor.v       | shr_mono              |
| T-bor-lft (for mut)   | uniq_bor.v      | uniq_mono             |
| C-subtype             | type_context.v  | subtype_tctx_incl     |
| C-copy                | type_context.v  | copy_tctx_incl        |
| C-split-bor (for shr) | product_split.v | tctx_split_shr_prod2  |
| C-split-bor (for mut) | product_split.v | tctx_split_uniq_prod2 |
| C-share               | borrow.v        | tctx_share            |
| C-borrow              | borrow.v        | tctx_borrow           |
| C-reborrow            | uniq_bor.v      | tctx_reborrow_uniq    |
| Tread-own-copy        | own.v           | read_own_copy         |
| Tread-own-move        | own.v           | read_own_move         |
| Tread-bor (for shr)   | shr_bor.v       | read_shr              |
| Tread-bor (for mut)   | uniq_bor.v      | read_uniq             |
| Twrite-own            | own.v           | write_own             |
| Twrite-bor            | uniq_bor.v      | write_uniq            |
| S-num                 | int.v           | type_int_instr        |
| S-nat-leq             | int.v           | type_le_instr         |
| S-new                 | own.v           | type_new_instr        |
| S-delete              | own.v           | type_delete_instr     |
| S-deref               | programs.v      | type_deref_instr      |
| S-assign              | programs.v      | type_assign_instr     |
| F-consequence         | programs.v      | typed_body_mono       |
| F-let                 | programs.v      | type_let'             |
| F-letcont             | cont.v          | type_cont             |
| F-jump                | cont.v          | type_jump             |
| F-newlft              | programs.v      | type_newlft           |
| F-endlft              | programs.v      | type_endlft           |
| F-call                | function.v      | type_call'            |

Some of these lemmas are called `something'` because the version without the `'` is a derived, more speicalized form used together with our eauto-based `solve_typing` tactic.  You can see this tactic in action in the [examples](theories/typing/examples) subfolder.

### Lifetime Logic Rules

The files in [lifetime](theories/lifetime) prove the lifetime logic, with the
core rules being proven in the [model](theories/lifetime/model) subfolder and
then sealed behind a module signature in
[lifetime.v](theories/lifetime/lifetime.v).


| Proof Rule        | File                | Lemma                |
|-------------------|---------------------|----------------------|
| LftL-begin        | model/creation.v    | lft_create           |
| LftL-tok-fract    | model/primitive.v   | lft_tok_fractional   |
| LftL-not-own-end  | model/primitive.v   | lft_tok_dead         |
| LftL-end-persist  | model/definitions.v | lft_dead_persistent  |
| LftL-borrow       | model/borrow.v      | bor_create           |
| LftL-bor-split    | model/bor_sep.v     | bor_sep              |
| LftL-bor-acc      | lifetime.v          | bor_acc              |
| LftL-bor-shorten  | model/primitive.v   | bor_shorten          |
| LftL-incl-isect   | model/primitive.v   | lft_intersect_incl_l |
| LftL-incl-glb     | model/primitive.v   | lft_incl_glb         |
| LftL-tok-inter    | model/primitive.v   | lft_tok_sep          |
| LftL-end-inter    | model/primitive.v   | lft_dead_or          |
| LftL-tok-unit     | model/primitive.v   | lft_tok_static       |
| LftL-end-unit     | model/primitive.v   | lft_dead_static      |
| LftL-reborrow     | lifetime.v          | rebor                |
| LftL-bor-fracture | frac_borrow.v       | bor_fracture         |
| LftL-fract-acc    | frac_borrow.v       | frac_bor_atomic_acc  |
| LftL-bor-na       | na_borrow.v         | bor_na               |
| LftL-na-acc       | na_borrow.v         | na_bor_acc           |

## For Developers: How to update the Iris dependency

* Do the change in Iris, push it.
* Wait for CI to publish a new Iris version on the opam archive, then run
  `opam update iris-dev`.
* In lambdaRust, change the `opam` file to depend on the new version.
* Run `make build-dep` (in lambdaRust) to install the new version of Iris.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.
