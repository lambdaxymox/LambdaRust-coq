From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Section init_prod.
  Context `{!typeGS Σ}.

  Definition init_prod : val :=
    fn: ["x"; "y"] :=
       let: "x'" := !"x" in let: "y'" := !"y" in
       let: "r" := new [ #2] in
       "r" +ₗ #0 <- "x'";; "r" +ₗ #1 <- "y'";;
       delete [ #1; "x"] ;; delete [ #1; "y"] ;; return: ["r"].

  Lemma init_prod_type : typed_val init_prod (fn(∅; int, int) → Π[int;int]).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([] ϝ ret p). inv_vec p=>x y. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (y'). simpl_subst.
    iApply (type_new_subtype (Π[uninit 1; uninit 1])); [solve_typing..|].
      iIntros (r). simpl_subst. unfold Z.to_nat, Pos.to_nat; simpl.
    iApply (type_assign (own_ptr 2 (uninit 1))); [solve_typing..|].
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End init_prod.
