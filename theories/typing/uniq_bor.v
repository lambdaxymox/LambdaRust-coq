From iris.proofmode Require Import tactics.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import util lft_contexts type_context programs.
Set Default Proof Using "Type".

Section uniq_bor.
  Context `{!typeGS Σ}.

  Program Definition uniq_bor (κ:lft) (ty:type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => &{κ} (l ↦∗: ty.(ty_own) tid)
         | _ => False
         end;
       ty_shr κ' tid l :=
         ∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ⊓κ']
               ={F}[F∖↑shrN]▷=∗ ty.(ty_shr) (κ⊓κ') tid l' ∗ q.[κ⊓κ']
    |}%I.
  Next Obligation. by iIntros (q ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    move=> κ ty N κ' l tid ??/=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as ([|[[|l'|]|][]]) "Hb"; first solve_ndisj;
      (iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]"; first solve_ndisj);
      try (iMod (bor_persistent with "LFT Hb2 Htok") as "[>[] _]"; solve_ndisj).
    iFrame. iExists l'. subst. rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$"; first solve_ndisj.
    iApply delay_sharing_nested; try done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid l. iIntros "#Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iAssert (κ0⊓κ' ⊑ κ0⊓κ)%I as "#Hκ0".
    { iApply lft_intersect_mono. iApply lft_incl_refl. done. }
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    iIntros "!> * % Htok". iApply (step_fupd_mask_mono F _ (F∖↑shrN)); try solve_ndisj.
    iMod (lft_incl_acc with "Hκ0 Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hvs" with "[%] Htok") as "Hvs'"; first solve_ndisj. iModIntro. iNext.
    iMod "Hvs'" as "[#Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty_shr_mono with "Hκ0").
  Qed.

  Global Instance uniq_bor_wf κ ty `{!TyWf ty} : TyWf (uniq_bor κ ty) :=
    { ty_lfts := [κ]; ty_wf_E := ty.(ty_wf_E) ++ ty_outlives_E ty κ }.

  Lemma uniq_type_incl κ1 κ2 ty1 ty2 :
    κ2 ⊑ κ1 -∗
    ▷ type_equal ty1 ty2 -∗
    type_incl (uniq_bor κ1 ty1) (uniq_bor κ2 ty2).
  Proof.
    iIntros "#Hlft #Hty". iSplit; first done.
    iSplit; iModIntro.
    - iIntros (? [|[[]|][]]) "H"; try done.
      iApply (bor_shorten with "Hlft"). iApply bor_iff; last done.
      iNext. iModIntro.
      iDestruct "Hty" as "(_ & Hty & _)".
      iSplit; iIntros "H"; iDestruct "H" as (vl) "[??]";
      iExists vl; iFrame; by iApply "Hty".
    - iIntros (κ ??) "H". iAssert (κ2 ⊓ κ ⊑ κ1 ⊓ κ)%I as "#Hincl'".
      { iApply lft_intersect_mono; first done. iApply lft_incl_refl. }
      iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'. iIntros "{$Hbor}!> %%% Htok".
      iMod (lft_incl_acc with "Hincl' Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      iMod ("Hupd" with "[%] Htok") as "Hupd'"; try done. iModIntro. iNext.
      iMod "Hupd'" as "[H Htok]". iMod ("Hclose" with "Htok") as "$".
      iDestruct "Hty" as "(_ & _ & Hty)".
      iApply ty_shr_mono; last by iApply "Hty".
      done.
  Qed.

  Global Instance uniq_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) uniq_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2. rewrite eqtype_unfold=>Hty. iIntros (??) "HL".
    iDestruct (Hty with "HL") as "#Hty". iDestruct (Hκ with "HL") as "#Hκ".
    iIntros "!> #HE".
    iApply uniq_type_incl.
    - iDestruct ("Hκ" with "HE") as %H.
      apply lft_incl_syn_sem in H. iApply H.
    - iNext. iApply "Hty". done.
  Qed.
  Global Instance uniq_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) uniq_bor.
  Proof. intros ??????. apply uniq_mono. done. by symmetry. Qed.
  Global Instance uniq_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) uniq_bor.
  Proof. intros ??[]; split; by apply uniq_mono. Qed.

  Global Instance uniq_type_contractive κ : TypeContractive (uniq_bor κ).
  Proof. solve_type_proper. Qed.

  Global Instance uniq_ne κ : NonExpansive (uniq_bor κ).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance uniq_send κ ty :
    Send ty → Send (uniq_bor κ ty).
  Proof.
    iIntros (Hsend tid1 tid2 [|[[]|][]]) "H"; try done.
    iApply bor_iff; last done. iNext. iModIntro. iApply bi.equiv_iff.
    do 3 f_equiv. iSplit; iIntros "."; by iApply Hsend.
  Qed.

  Global Instance uniq_sync κ ty :
    Sync ty → Sync (uniq_bor κ ty).
  Proof.
    iIntros (Hsync κ' tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists l'. iFrame "Hm". iModIntro. iIntros (F q) "% Htok".
    iMod ("Hshr" with "[] Htok") as "Hfin"; first done. iClear "Hshr".
    iModIntro. iNext. iMod "Hfin" as "[Hshr $]". iApply Hsync. done.
  Qed.
End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeGS Σ}.

  Lemma uniq_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_incl E L κ2 κ1 → eqtype E L ty1 ty2 →
    subtype E L (&uniq{κ1}ty1) (&uniq{κ2}ty2).
  Proof. by intros; apply uniq_mono. Qed.
  Lemma uniq_proper' E L κ1 κ2 ty1 ty2 :
    lctx_lft_eq E L κ1 κ2 → eqtype E L ty1 ty2 → eqtype E L (&uniq{κ1}ty1) (&uniq{κ2}ty2).
  Proof. by intros; apply uniq_proper. Qed.

  Lemma tctx_reborrow_uniq E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &uniq{κ'}ty; p ◁{κ'} &uniq{κ}ty].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT HE HL H". iDestruct (Hκκ' with "HL HE") as %H.
    iDestruct (lft_incl_syn_sem κ' κ H) as "Hκκ'".
    iFrame. rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|]) "[% Hb]"; try done.
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]". done. iModIntro.
    iSplitL "Hb"; iExists _; auto.
  Qed.

  Lemma tctx_extract_hasty_reborrow E L p ty ty' κ κ' T :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' →
    tctx_extract_hasty E L p (&uniq{κ'}ty) ((p ◁ &uniq{κ}ty')::T)
                       ((p ◁{κ'} &uniq{κ}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]). rewrite tctx_reborrow_uniq //.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, uniq_mono'.
  Qed.

  Lemma read_uniq E L κ ty :
    Copy ty → lctx_lft_alive E L κ → ⊢ typed_read E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hcopy Halive) "!>".
    iIntros ([[]|] tid F qmax qL ?) "#LFT #HE Htl HL Hown"; try done.
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first solve_ndisj.
    iMod (bor_acc with "LFT Hown Hκ") as "[H↦ Hclose']"; first solve_ndisj.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". iIntros "!>".
    iExists _, _, _. iSplit; first done. iFrame "∗#". iIntros "H↦".
    iMod ("Hclose'" with "[H↦]") as "[$ Htok]". by iExists _; iFrame.
    by iMod ("Hclose" with "Htok") as "($ & $ & $)".
  Qed.

  Lemma write_uniq E L κ ty :
    lctx_lft_alive E L κ → ⊢ typed_write E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    rewrite typed_write_eq. iIntros (Halive) "!>".
    iIntros ([[]|] tid F qmax qL ?) "#LFT HE HL Hown"; try done.
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    iMod (bor_acc with "LFT Hown Htok") as "[H↦ Hclose']"; first solve_ndisj.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iModIntro. iExists _, _. iSplit; first done.
    iFrame. iIntros "Hown". iDestruct "Hown" as (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[$ Htok]". by iExists _; iFrame.
    by iMod ("Hclose" with "Htok") as "($ & $ & $)".
  Qed.
End typing.

Global Hint Resolve uniq_mono' uniq_proper' write_uniq read_uniq : lrust_typing.
Global Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
