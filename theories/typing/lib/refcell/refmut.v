From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing util.
From lrust.typing.lib.refcell Require Import refcell.
Set Default Proof Using "Type".

Section refmut.
  Context `{!typeGS Σ, !refcellG Σ}.

  (* The Rust type looks as follows (after some unfolding):

     pub struct RefMut<'b, T: ?Sized + 'b> {
       value: &'b mut T,
       borrow: &'b Cell<BorrowFlag>,
     }

     In other words, we have a pointer to the data, and a pointer
     to the refcount field of the RefCell. *)

  Program Definition refmut (α : lft) (ty : type) :=
    tc_opaque
    {| ty_size := 2;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc lv);  #(LitLoc lrc) ] =>
           ∃ ν q γ β ty', &{α ⊓ ν}(lv ↦∗: ty.(ty_own) tid) ∗
             α ⊑ β ∗ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             q.[ν] ∗ own γ (◯ writing_stR q ν)
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (lv lrc : loc),
           &frac{κ} (λ q, l↦∗{q} [ #lv; #lrc]) ∗
           □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[α ⊓ κ]
             ={F}[F∖↑shrN]▷=∗ ty.(ty_shr) (α ⊓ κ) tid lv ∗ q.[α ⊓ κ] |}%I.
  Next Obligation.
    iIntros (???[|[[]|][|[[]|][]]]); try iIntros "[]". by iIntros "_".
  Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb". done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (ty') "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hαβ H]". done.
    iMod (bor_persistent with "LFT Hαβ Htok") as "[#Hαβ $]". done.
    iMod (bor_sep with "LFT H") as "[_ H]". done.
    iMod (bor_sep with "LFT H") as "[H _]". done.
    iMod (bor_fracture (λ q, (q' * q).[ν])%I with "LFT [H]") as "H". done.
    { by rewrite Qp_mul_1_r. }
    iDestruct (frac_bor_lft_incl with "LFT H") as "#Hκν". iClear "H".
    iExists _, _. iFrame "H↦". iApply delay_sharing_nested; try done.
    rewrite -assoc. iApply lft_intersect_mono; first by iApply lft_incl_refl.
    iApply lft_incl_glb; first done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (??????) "#? H". iDestruct "H" as (lv lrc) "[#Hf #H]".
    iExists _, _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!> * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_intersect_mono. iApply lft_incl_refl. done.
  Qed.

  Global Instance refmut_wf α ty `{!TyWf ty} : TyWf (refmut α ty) :=
    { ty_lfts := [α]; ty_wf_E := ty_wf_E ty ++ ty_outlives_E ty α }.

  Global Instance refmut_type_contractive α : TypeContractive (refmut α).
  Proof. solve_type_proper. Qed.
  Global Instance refmut_ne α : NonExpansive (refmut α).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance refmut_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) refmut.
  Proof.
    intros α1 α2 Hα ty1 ty2. rewrite eqtype_unfold=>Hty. iIntros (qmax qL) "HL".
    iDestruct (Hty with "HL") as "#Hty". iDestruct (Hα with "HL") as "#Hα".
    iIntros "!> #HE". iDestruct ("Hα" with "HE") as %Hα1α2.
    iDestruct ("Hty" with "HE") as "(%&#Ho&#Hs)". iSplit; [|iSplit; iModIntro].
    - done.
    - iIntros (tid [|[[]|][|[[]|][]]]) "H"=>//=.
      iDestruct "H" as (ν γ q' β ty') "(Hb & #H⊑ & #Hinv & Hν & Hown)".
      iExists ν, γ, q', β, ty'. iFrame "∗#". iSplit.
      + iApply bor_shorten; last iApply bor_iff; last done.
        * iApply lft_intersect_mono; first by iApply lft_incl_syn_sem.
          iApply lft_incl_refl.
        * iNext; iModIntro; iSplit; iIntros "H"; iDestruct "H" as (vl) "[??]";
          iExists vl; iFrame; by iApply "Ho".
      + iApply lft_incl_trans; last done. by iApply lft_incl_syn_sem.
    - iIntros (κ tid l) "H /=". iDestruct "H" as (lv lrc) "H". iExists lv, lrc.
      iDestruct "H" as "[$ #H]". iIntros "!> * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono; first by iApply lft_incl_syn_sem. iApply lft_incl_refl. }
      iMod ("H" with "[] Htok") as "Hshr"; first done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done.
      + iApply lft_intersect_mono. by iApply lft_incl_syn_sem. iApply lft_incl_refl.
      + by iApply "Hs".
  Qed.
  Global Instance refmut_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) refmut.
  Proof. intros ??????. by apply refmut_mono. Qed.
  Lemma refmut_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (refmut α1 ty1) (refmut α2 ty2) .
  Proof. intros. by eapply refmut_mono. Qed.
  Global Instance refmut_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E  L) refmut.
  Proof. intros ??[]???. split; by apply refmut_mono'. Qed.
  Lemma refmut_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (refmut α1 ty1) (refmut α2 ty2).
  Proof. intros. by eapply refmut_proper. Qed.
End refmut.

Global Hint Resolve refmut_mono' refmut_proper' : lrust_typing.
