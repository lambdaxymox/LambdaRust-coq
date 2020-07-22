From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.algebra Require Import frac.
From lrust.lifetime Require Export at_borrow.
Set Default Proof Using "Type".

Class frac_borG Σ := frac_borG_inG :> inG Σ fracR.

Definition frac_bor `{!invG Σ, !lftG Σ, !frac_borG Σ} κ (φ : Qp → iProp Σ) :=
  (∃ γ κ', κ ⊑ κ' ∗ &at{κ',lftN} (∃ q, φ q ∗ own γ q ∗
                       (⌜q = 1%Qp⌝ ∨ ∃ q', ⌜(q + q' = 1)%Qp⌝ ∗ q'.[κ'])))%I.
Notation "&frac{ κ }" := (frac_bor κ) (format "&frac{ κ }") : bi_scope.

Section frac_bor.
  Context `{!invG Σ, !lftG Σ, !frac_borG Σ} (φ : Qp → iProp Σ).
  Implicit Types E : coPset.

  Global Instance frac_bor_contractive κ n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (frac_bor κ).
  Proof. solve_contractive. Qed.
  Global Instance frac_bor_ne κ n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (frac_bor κ).
  Proof. solve_proper. Qed.
  Global Instance frac_bor_proper κ :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (frac_bor κ).
  Proof. solve_proper. Qed.

  Lemma frac_bor_iff κ φ' :
    ▷ □ (∀ q, φ q ↔ φ' q) -∗ &frac{κ} φ -∗ &frac{κ} φ'.
  Proof.
    iIntros "#Hφφ' H". iDestruct "H" as (γ κ') "[? Hφ]". iExists γ, κ'. iFrame.
    iApply (at_bor_iff with "[Hφφ'] Hφ"). iNext. iModIntro.
    iSplit; iIntros "H"; iDestruct "H" as (q) "[H ?]"; iExists q; iFrame; by iApply "Hφφ'".
  Qed.

  Global Instance frac_bor_persistent κ : Persistent (&frac{κ}φ) := _.

  Lemma bor_fracture E κ :
    ↑lftN ⊆ E → lft_ctx -∗ &{κ}(φ 1%Qp) ={E}=∗ &frac{κ}φ.
  Proof.
    iIntros (?) "#LFT Hφ". iMod (own_alloc 1%Qp) as (γ) "?". done.
    iMod (bor_acc_atomic_strong with "LFT Hφ") as "[H|[H† Hclose]]". done.
    - iDestruct "H" as (κ') "(#Hκκ' & Hφ & Hclose)".
      iMod ("Hclose" with "[] [-]") as "Hφ"; last first.
      { iExists γ, κ'. iFrame "#". iApply (bor_share_lftN with "Hφ"); auto. }
      { iExists 1%Qp. iFrame. eauto. }
      iIntros "!>Hφ H†!>". iNext. iDestruct "Hφ" as (q') "(Hφ & _ & [%|Hκ])". by subst.
      iDestruct "Hκ" as (q'') "[_ Hκ]".
      iDestruct (lft_tok_dead with "Hκ H†") as "[]".
    - iMod "Hclose" as "_"; last first.
      iExists γ, κ. iSplitR. by iApply lft_incl_refl.
      by iApply at_bor_fake_lftN.
  Qed.

  Lemma frac_bor_atomic_acc E κ :
    ↑lftN ⊆ E →
    lft_ctx -∗ &frac{κ}φ ={E,E∖↑lftN}=∗ (∃ q, ▷ φ q ∗ (▷ φ q ={E∖↑lftN,E}=∗ True))
                                      ∨ [†κ] ∗ |={E∖↑lftN,E}=> True.
  Proof.
    iIntros (?) "#LFT #Hφ". iDestruct "Hφ" as (γ κ') "[Hκκ' Hshr]".
    iMod (at_bor_acc_lftN with "LFT Hshr") as "[[Hφ Hclose]|[H† Hclose]]"; try done.
    - iLeft. iDestruct "Hφ" as (q) "(Hφ & Hγ & H)". iExists q. iFrame.
      iIntros "!>Hφ". iApply "Hclose". iExists q. iFrame.
    - iRight. iMod "Hclose" as "_". iMod (lft_incl_dead with "Hκκ' H†") as "$". done.
      iApply fupd_intro_mask. set_solver. done.
  Qed.

  Lemma frac_bor_acc' E q κ :
    ↑lftN ⊆ E →
    lft_ctx -∗ □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ∗ φ q2) -∗
    &frac{κ}φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ φ q' ∗ (▷ φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT #Hφ Hfrac Hκ". unfold frac_bor.
    iDestruct "Hfrac" as (γ κ') "#[#Hκκ' Hshr]".
    iMod (lft_incl_acc with "Hκκ' Hκ") as (qκ') "[[Hκ1 Hκ2] Hclose]". done.
    iMod (at_bor_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']"; try done.
    iDestruct "H" as (qφ) "(Hφqφ & >Hown & Hq)".
    destruct (Qp_lower_bound (qκ'/2) (qφ/2)) as (qq & qκ'0 & qφ0 & Hqκ' & Hqφ).
    iExists qq.
    iAssert (▷ (φ qq ∗ φ (qφ0 + qφ / 2)))%Qp%I with "[Hφqφ]" as "[$ Hqφ]".
    { iNext. rewrite -{1}(Qp_div_2 qφ) {1}Hqφ. iApply "Hφ". by rewrite assoc. }
    rewrite -{1}(Qp_div_2 qφ) {1}Hqφ -assoc {1}Hqκ'.
    iDestruct "Hκ2" as "[Hκq Hκqκ0]". iDestruct "Hown" as "[Hownq Hown]".
    iMod ("Hclose'" with "[Hqφ Hq Hown Hκq]") as "Hκ1".
    { iNext. iExists _. iFrame. iRight. iDestruct "Hq" as "[%|Hq]".
      - subst. iExists qq. iIntros "{$Hκq}!%".
        by rewrite (comm _ qφ0) -assoc (comm _ qφ0) -Hqφ Qp_div_2.
      - iDestruct "Hq" as (q') "[% Hq'κ]". iExists (qq + q')%Qp.
        iIntros "{$Hκq $Hq'κ}!%". by rewrite assoc (comm _ _ qq) assoc -Hqφ Qp_div_2. }
    clear Hqφ qφ qφ0. iIntros "!>Hqφ".
    iMod (at_bor_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']"; try done.
    iDestruct "H" as (qφ) "(Hφqφ & >Hown & >[%|Hq])".
    { subst. iCombine "Hown" "Hownq" as "Hown".
      by iDestruct (own_valid with "Hown") as %Hval%Qp_not_plus_q_ge_1. }
    iDestruct "Hq" as (q') "[Hqφq' Hq'κ]". iCombine "Hown" "Hownq" as "Hown".
    iDestruct (own_valid with "Hown") as %Hval. iDestruct "Hqφq'" as %Hqφq'.
    assert (0 < q'-qq ∨ qq = q')%Qc as [Hq'q|<-].
    { change (qφ + qq ≤ 1)%Qc in Hval. apply Qp_eq in Hqφq'. simpl in Hval, Hqφq'.
      rewrite <-Hqφq', <-Qcplus_le_mono_l in Hval. apply Qcle_lt_or_eq in Hval.
      destruct Hval as [Hval|Hval].
      by left; apply ->Qclt_minus_iff. right; apply Qp_eq, Qc_is_canon. by rewrite Hval. }
    - assert (q' = mk_Qp _ Hq'q + qq)%Qp as ->. { apply Qp_eq. simpl. ring. }
      iDestruct "Hq'κ" as "[Hq'qκ Hqκ]".
      iMod ("Hclose'" with "[Hqφ Hφqφ Hown Hq'qκ]") as "Hqκ2".
      { iNext. iExists (qφ + qq)%Qp. iFrame. iSplitR "Hq'qκ". by iApply "Hφ"; iFrame.
        iRight. iExists _. iIntros "{$Hq'qκ}!%".
        revert Hqφq'. rewrite !Qp_eq. move=>/=<-. ring. }
      iApply "Hclose". iFrame. rewrite Hqκ'. by iFrame.
    - iMod ("Hclose'" with "[Hqφ Hφqφ Hown]") as "Hqκ2".
      { iNext. iExists (qφ ⋅ qq)%Qp. iFrame. iSplitL. by iApply "Hφ"; iFrame. auto. }
      iApply "Hclose". iFrame. rewrite Hqκ'. by iFrame.
  Qed.

  Lemma frac_bor_acc E q κ `{!Fractional φ} :
    ↑lftN ⊆ E →
    lft_ctx -∗ &frac{κ}φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ φ q' ∗ (▷ φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros (?) "LFT". iApply (frac_bor_acc' with "LFT"). done.
    iIntros "!#*". rewrite fractional. iSplit; auto.
  Qed.

  Lemma frac_bor_shorten κ κ' : κ ⊑ κ' -∗ &frac{κ'}φ -∗ &frac{κ}φ.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (γ κ0) "[#H⊑ ?]". iExists γ, κ0. iFrame.
    iApply (lft_incl_trans with "Hκκ' []"). auto.
  Qed.

  Lemma frac_bor_fake E κ :
    ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &frac{κ}φ.
  Proof.
    iIntros (?) "#LFT#H†". iApply (bor_fracture with "LFT [>]"); first done.
    by iApply (bor_fake with "LFT").
  Qed.
End frac_bor.

Lemma frac_bor_lft_incl `{!invG Σ, !lftG Σ, !frac_borG Σ} κ κ' q:
  lft_ctx -∗ &frac{κ}(λ q', (q * q').[κ']) -∗ κ ⊑ κ'.
Proof.
  iIntros "#LFT#Hbor". iApply lft_incl_intro. iModIntro. iSplitR.
  - iIntros (q') "Hκ'".
    iMod (frac_bor_acc with "LFT Hbor Hκ'") as (q'') "[>? Hclose]". done.
    iExists _. iFrame. iIntros "!>Hκ'". iApply "Hclose". auto.
  - iIntros "H†'".
    iMod (frac_bor_atomic_acc with "LFT Hbor") as "[H|[$ $]]". done.
    iDestruct "H" as (q') "[>Hκ' _]".
    iDestruct (lft_tok_dead with "Hκ' H†'") as "[]".
Qed.

Typeclasses Opaque frac_bor.
