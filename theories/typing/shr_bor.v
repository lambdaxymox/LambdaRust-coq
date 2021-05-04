From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import lft_contexts type_context programs.
Set Default Proof Using "Type".

Section shr_bor.
  Context `{!typeG Σ}.

  Program Definition shr_bor (κ : lft) (ty : type) : type :=
    {| st_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => ty.(ty_shr) κ tid l
         | _ => False
         end%I |}.
  Next Obligation. by iIntros (κ ty tid [|[[]|][]]) "H". Qed.
  Next Obligation. intros κ ty tid [|[[]|][]]; apply _. Qed.

  Global Instance shr_bor_wf κ ty `{!TyWf ty} : TyWf (shr_bor κ ty) :=
    { ty_lfts := [κ]; ty_wf_E := ty.(ty_wf_E) ++ ty_outlives_E ty κ }.

  Lemma shr_type_incl κ1 κ2 ty1 ty2 :
    κ2 ⊑ κ1 -∗ type_incl ty1 ty2 -∗ type_incl (shr_bor κ1 ty1) (shr_bor κ2 ty2).
  Proof.
    iIntros "#Hκ #[_ [_ Hty]]". iApply type_incl_simple_type. simpl.
    iIntros "!>" (tid [|[[]|][]]) "H"; try done. iApply "Hty".
    iApply (ty1.(ty_shr_mono) with "Hκ"). done.
  Qed.

  Global Instance shr_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> subtype E L ==> subtype E L) shr_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 Hty.
    iIntros (??) "/= HL". iDestruct (Hκ with "HL") as "#Hincl".
    iDestruct (Hty with "HL") as "#Hty". iIntros "!> #HE".
    iDestruct ("Hincl" with "HE") as "%".
    iApply shr_type_incl.
    - by iApply lft_incl_syn_sem.
    - by iApply "Hty".
  Qed.
  Global Instance shr_mono_flip E L :
    Proper (lctx_lft_incl E L ==> flip (subtype E L) ==> flip (subtype E L)) shr_bor.
  Proof. intros ??????. by apply shr_mono. Qed.
  Global Instance shr_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) shr_bor.
  Proof. intros ??[] ??[]. by split; apply shr_mono. Qed.

  Global Instance shr_type_contractive κ : TypeContractive (shr_bor κ).
  Proof.
    intros n ???. apply: ty_of_st_type_ne. destruct n; first done.
    solve_type_proper.
  Qed.

  Global Instance shr_ne κ : NonExpansive (shr_bor κ).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance shr_send κ ty :
    Sync ty → Send (shr_bor κ ty).
  Proof. by iIntros (Hsync tid1 tid2 [|[[]|][]]) "H"; try iApply Hsync. Qed.
End shr_bor.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma shr_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_incl E L κ2 κ1 → subtype E L ty1 ty2 →
    subtype E L (&shr{κ1}ty1) (&shr{κ2}ty2).
  Proof. by intros; apply shr_mono. Qed.
  Lemma shr_proper' E L κ1 κ2 ty1 ty2 :
    lctx_lft_eq E L κ1 κ2 → eqtype E L ty1 ty2 → eqtype E L (&shr{κ1}ty1) (&shr{κ2}ty2).
  Proof. by intros; apply shr_proper. Qed.

  Lemma tctx_reborrow_shr E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [p ◁ &shr{κ}ty] [p ◁ &shr{κ'}ty; p ◁{κ} &shr{κ}ty].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT #HE HL [H _]". iDestruct (Hκκ' with "HL HE") as "%".
    iFrame. rewrite /tctx_interp /=.
    iDestruct "H" as ([[]|]) "[% #Hshr]"; try done. iModIntro. iSplit.
    - iExists _. iSplit. done. iApply (ty_shr_mono with "[] Hshr").
      by iApply lft_incl_syn_sem.
    - iSplit=> //. iExists _. auto.
  Qed.

  Lemma read_shr E L κ ty :
    Copy ty → lctx_lft_alive E L κ → ⊢ typed_read E L (&shr{κ}ty) ty (&shr{κ}ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hcopy Halive) "!>".
    iIntros ([[]|] tid F qmax qL ?) "#LFT #HE Htl HL #Hshr"; try done.
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first solve_ndisj.
    iMod (copy_shr_acc with "LFT Hshr Htl Hκ") as (q') "(Htl & H↦ & Hcl)"; first solve_ndisj.
    { rewrite ->shr_locsE_shrN. solve_ndisj. }
    iDestruct "H↦" as (vl) "[>Hmt #Hown]". iModIntro. iExists _, _, _.
    iFrame "∗#". iSplit; first done. iIntros "Hmt".
    iMod ("Hcl" with "Htl [Hmt]") as "[$ Hκ]"; first by iExists _; iFrame.
    iApply ("Hclose" with "Hκ").
  Qed.
End typing.

Global Hint Resolve shr_mono' shr_proper' read_shr : lrust_typing.
