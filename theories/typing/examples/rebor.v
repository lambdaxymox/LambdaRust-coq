From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Section rebor.
  Context `{!typeGS Σ}.

  Definition rebor : val :=
    fn: ["t1"; "t2"] :=
       Newlft;;
       letalloc: "x" <- "t1" in
       let: "x'" := !"x" in let: "y" := "x'" +ₗ #0 in
       "x" <- "t2";;
       let: "y'" := !"y" in
       letalloc: "r" <- "y'" in
       Endlft ;; delete [ #2; "t1"] ;; delete [ #2; "t2"] ;;
                 delete [ #1; "x"] ;; return: ["r"].

  Lemma rebor_type :
    typed_val rebor (fn(∅; Π[int; int], Π[int; int]) → int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([] ϝ ret p). inv_vec p=>t1 t2. simpl_subst.
    iApply (type_newlft []). iIntros (α).
    iApply (type_letalloc_1 (&uniq{α}(Π[int; int]))); [solve_typing..|]. iIntros (x). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iApply (type_letpath (&uniq{α}int)); [solve_typing|]. iIntros (y). simpl_subst.
    iApply (type_assign _ (&uniq{α}(Π[int; int]))); [solve_typing..|].
    iApply type_deref; [solve_typing..|]. iIntros (y'). simpl_subst.
    iApply type_letalloc_1; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_endlft.
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End rebor.
