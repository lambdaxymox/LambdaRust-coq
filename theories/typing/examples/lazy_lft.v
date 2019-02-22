From iris.proofmode Require Import tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section lazy_lft.
  Context `{!typeG Σ}.

  Definition lazy_lft : val :=
    funrec: <> [] :=
      Newlft;;
      let: "t" := new [ #2] in let: "f" := new [ #1] in let: "g" := new [ #1] in
      let: "42" := #42 in "f" <- "42";;
      "t" +ₗ #0 <- "f";; "t" +ₗ #1 <- "f";;
      let: "t0'" := !("t" +ₗ #0) in "t0'";;
      let: "23" := #23 in "g" <- "23";;
      "t" +ₗ #1 <- "g";;
      let: "r" := new [ #0] in
      Endlft;; delete [ #2; "t"];; delete [ #1; "f"];; delete [ #1; "g"];; return: ["r"].

  Lemma lazy_lft_type : typed_val lazy_lft (fn(∅) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([] ϝ ret p). inv_vec p. simpl_subst.
    iApply (type_newlft []). iIntros (α).
    iApply (type_new_subtype (Π[uninit 1;uninit 1])); [solve_typing..|].
      iIntros (t). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (f). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (g). simpl_subst.
    iApply type_int. iIntros (v42). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply (type_assign _ (&shr{α}_)); [solve_typing..|].
    iApply type_assign; [solve_typing..|].
    iApply type_deref; [solve_typing..|]. iIntros (t0'). simpl_subst.
    iApply type_letpath; [solve_typing|]. iIntros (dummy). simpl_subst.
    iApply type_int. iIntros (v23). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply (type_assign _ (&shr{α}int)); [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_endlft; [solve_typing..|].
    iApply (type_delete (Π[&shr{α}_;&shr{α}_])%T); [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End lazy_lft.
