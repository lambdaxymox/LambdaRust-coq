From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lifetime Require Import reborrow frac_borrow.
From lrust.lang Require Import heap.
From lrust.typing Require Export uniq_bor shr_bor own.
From lrust.typing Require Import lft_contexts type_context perm typing.

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{typeG Σ}.

  Lemma tctx_borrow E L p n ty κ :
    tctx_incl E L [TCtx_hasty p (own n ty)]
                  [TCtx_hasty p (&uniq{κ}ty); TCtx_blocked p κ (own n ty)].
  Proof.
    iIntros (tid ??) "#LFT $ $ H".
    rewrite /tctx_interp big_sepL_singleton big_sepL_cons big_sepL_singleton.
    iDestruct "H" as (v) "[% Hown]". iDestruct "Hown" as (l) "(EQ & Hmt & ?)".
    iDestruct "EQ" as %[=->]. iMod (bor_create with "LFT Hmt") as "[Hbor Hext]". done.
    iModIntro. iSplitL "Hbor".
    - iExists _. iSplit. done. iExists _, _. erewrite <-uPred.iff_refl. eauto.
    - iExists _. iSplit. done. iIntros "H†". iExists _. iFrame. iSplitR. by eauto.
        by iMod ("Hext" with "H†") as "$".
  Qed.
  
  Lemma tctx_reborrow_uniq E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [TCtx_hasty p (&uniq{κ}ty)]
                  [TCtx_hasty p (&uniq{κ'}ty); TCtx_blocked p κ (&uniq{κ}ty)].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT HE HL H".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iDestruct (llctx_interp_persist with "HL") as "#HL'". iFrame "HE HL".
    iDestruct (Hκκ' with "HE' HL'") as "Hκκ'".
    rewrite /tctx_interp big_sepL_singleton big_sepL_cons big_sepL_singleton.
    iDestruct "H" as (v) "[% Hown]". iDestruct "Hown" as (l P) "[[EQ #Hiff] Hb]".
    iDestruct "EQ" as %[=->]. iMod (bor_iff with "LFT [] Hb") as "Hb". done. by eauto.
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]". done. iModIntro. iSplitL "Hb".
    - iExists _. iSplit. done. iExists _, _. erewrite <-uPred.iff_refl. eauto.
    - iExists _. iSplit. done. iIntros "#H†".
      iMod ("Hext" with ">[]") as "Hb". by iApply (lft_incl_dead with "Hκκ' H†").
      iExists _, _. erewrite <-uPred.iff_refl. eauto.
  Qed.


  Lemma typed_deref_uniq_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &uniq{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_acc_cons with "LFT H↦ Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & Hown & H†)".
    subst. rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose'" with "*[H↦ Hown H†][]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod (bor_sep _ _ _ (l' ↦∗: ty_own ty tid) with "LFT Hbor") as "[_ Hbor]". done.
      iMod ("Hclose" with "Htok") as "$". iFrame "#". iExists _, _.
      iFrame. iSplitR. done. by rewrite -uPred.iff_refl.
    - iFrame "H↦ H† Hown".
    - iIntros "!>(?&?&?)!>". iNext. iExists _.
      rewrite -heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame.
  Qed.

  Lemma typed_deref_uniq_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &uniq{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &uniq{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & Htok & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑1 Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_exists with "LFT H↦") as (vl) "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]". done.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor". done.
    iMod (bor_exists with "LFT Hbor") as (P') "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H Hbor]". done.
    iMod (bor_persistent_tok with "LFT H Htok") as "[[>% #HP'iff] Htok]". done. subst.
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']". done.
    rewrite heap_mapsto_vec_singleton.
    iApply (wp_fupd_step  _ (⊤∖↑lftN) with "[Hbor]"); try done.
      by iApply (bor_unnest with "LFT Hbor").
    wp_read. iIntros "!> Hbor". iFrame "#". iSplitL "Hbor".
    - iExists _, _. iSplitR. by auto.
      iApply (bor_shorten with "[] Hbor").
      iApply (lft_incl_glb with "H⊑2"). iApply lft_incl_refl.
    - iApply ("Hclose" with ">"). by iMod ("Hclose'" with "[$H↦]") as "[_ $]".
  Qed.

  Lemma typed_deref_shr_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &shr{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &shr{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & [Htok1 Htok2]) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok1") as (q'') "[Htok1 Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iMod (lft_incl_acc with "H⊑ Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[Hshr Htok2]{$H⊑}". iMod ("Hclose''" with "Htok2") as "$".
      iSplitL "Hshr"; first by iExists _; auto. iApply ("Hclose" with ">").
      iFrame. iApply "Hclose'". auto.
  Qed.

  Lemma typed_deref_shr_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &shr{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &shr{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & [Htok1 Htok2] & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq Hshr]".
    iDestruct "Heq" as %[=->]. iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (lft_incl_acc with "H⊑1 Htok1") as (q') "[Htok1 Hclose]". done.
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ' ⊑ κ'' ∪ κ')%I as "#H⊑3".
    { iApply (lft_incl_glb with "H⊑2 []"). iApply lft_incl_refl. }
    iMod (lft_incl_acc with "[] Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    { iApply (lft_incl_trans with "[]"); done. }
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[#Hshr Htok2]{$H⊑1}".
      iMod ("Hclose''" with "Htok2") as "$". iSplitR.
      * iExists _. iSplitR. done. by iApply (ty_shr_mono with "LFT H⊑3 Hshr").
      * iApply ("Hclose" with ">"). iApply ("Hclose'" with "[$H↦]").
  Qed.

End borrow.