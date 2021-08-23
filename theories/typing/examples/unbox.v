From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Section unbox.
  Context `{!typeGS Σ}.

  Definition unbox : val :=
    fn: ["b"] :=
       let: "b'" := !"b" in let: "bx" := !"b'" in
       letalloc: "r" <- "bx" +ₗ #0 in
       delete [ #1; "b"] ;; return: ["r"].

  Lemma ubox_type :
    typed_val unbox (fn(∀ α, ∅; &uniq{α}(box(Π[int; int]))) → &uniq{α}int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret b). inv_vec b=>b. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (b'); simpl_subst.
    iApply type_deref_uniq_own; [solve_typing..|]. iIntros (bx); simpl_subst.
    iApply type_letalloc_1; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End unbox.
