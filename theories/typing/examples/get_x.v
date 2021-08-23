From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Section get_x.
  Context `{!typeGS Σ}.

  Definition get_x : val :=
    fn: ["p"] :=
       let: "p'" := !"p" in
       letalloc: "r" <- "p'" +ₗ #0 in
       delete [ #1; "p"] ;; return: ["r"].

  Lemma get_x_type :
    typed_val get_x (fn(∀ α, ∅; &uniq{α}(Π[int; int])) → &shr{α}int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret p).
    inv_vec p=>p. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (p'); simpl_subst.
    iApply (type_letalloc_1 (&shr{α}int)); [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End get_x.
