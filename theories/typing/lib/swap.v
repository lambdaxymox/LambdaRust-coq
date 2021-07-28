From iris.proofmode Require Import proofmode.
From lrust.lang.lib Require Import swap.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section swap.
  Context `{!typeGS Σ}.

  Definition swap ty : val :=
    fn: ["p1"; "p2"] :=
      let: "p1'" := !"p1" in
      let: "p2'" := !"p2" in
      swap ["p1'"; "p2'"; #ty.(ty_size)];;
      delete [ #1; "p1"];; delete [ #1; "p2"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma swap_type τ `{!TyWf τ} :
    typed_val (swap τ) (fn(∀ α, ∅; &uniq{α} τ, &uniq{α} τ) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret p).
      inv_vec p=>p1 p2. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (p1'). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (p2'). simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hk (H2 & H2' & H1 & H1' & _)".
    rewrite !tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose)";
      [solve_typing..|].
    iDestruct (uniq_is_ptr with "H1'") as (l1) "#H1eq". iDestruct "H1eq" as %[=->].
    iMod (bor_acc with "LFT H1' Hα1") as "[H1' Hclose1]"=>//.
    iDestruct "H1'" as (vl1) "[>H↦1 H1']".
    iDestruct (τ.(ty_size_eq) with "H1'") as "#>%".
    iDestruct (uniq_is_ptr with "H2'") as (l2) "#H2eq". iDestruct "H2eq" as %[=->].
    iMod (bor_acc with "LFT H2' Hα2") as "[H2' Hclose2]"=>//.
    iDestruct "H2'" as (vl2) "[>H↦2 H2']".
    iDestruct (τ.(ty_size_eq) with "H2'") as "#>%".
    wp_apply (wp_swap with "[$H↦1 $H↦2]"); try lia. iIntros "[H↦1 H↦2]". wp_seq.
    iMod ("Hclose" with "[>-Hna HL H1 H2 Hk] HL") as "HL".
    { iMod ("Hclose1" with "[H2' H↦1]") as "[_ $]"; first by iExists _; iFrame.
      by iMod ("Hclose2" with "[H1' H↦2]") as "[_ $]"; first by iExists _; iFrame. }
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ p1 ◁ box (uninit 1); p2 ◁ box (uninit 1) ]
      with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply (type_new _); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
End swap.
