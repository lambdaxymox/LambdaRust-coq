From lrust.lifetime Require Export lifetime_sig.
From lrust.lifetime.model Require definitions primitive accessors faking borrow
     borrow_sep reborrow creation.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Module Export lifetime : lifetime_sig.
  Definition lft := gmultiset positive.
  Include definitions.
  Include primitive.
  Include borrow.
  Include faking.
  Include borrow_sep.
  Include reborrow.
  Include accessors.
  Include creation.
End lifetime.

Notation lft_intersect_list l := (foldr lft_intersect static l).

Instance lft_inhabited : Inhabited lft := populate static.

Canonical lftC := leibnizC lft.

Section derived.
Context `{!invG Σ, !lftG Σ}.
Implicit Types κ : lft.

Lemma bor_acc_atomic_cons E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
    (▷ P ∗ ∀ Q, ▷ (▷ Q ={∅}=∗ ▷ P) -∗ ▷ Q ={E∖↑lftN,E}=∗ &{κ} Q) ∨
    ([†κ] ∗ |={E∖↑lftN,E}=> True).
Proof.
  iIntros (?) "#LFT HP".
  iMod (bor_acc_atomic_strong with "LFT HP") as "[H|[??]]"; first done.
  - iLeft. iDestruct "H" as (κ') "(#Hκκ' & $ & Hclose)". iIntros "!>* HPQ HQ".
    iMod ("Hclose" with "[HPQ] HQ") as "Hb".
    + iNext. iIntros "? _". by iApply "HPQ".
    + iApply (bor_shorten with "Hκκ' Hb").
  - iRight. by iFrame.
Qed.

Lemma bor_acc_atomic E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P ={E,E∖↑lftN}=∗
       (▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ &{κ}P)) ∨ ([†κ] ∗ |={E∖↑lftN,E}=> True).
Proof.
  iIntros (?) "#LFT HP".
  iMod (bor_acc_atomic_cons with "LFT HP") as "[[HP Hclose]|[? ?]]"; first done.
  - iLeft. iIntros "!> {$HP} HP". iMod ("Hclose" with "[] HP"); auto.
  - iRight. by iFrame.
Qed.

Lemma bor_acc_cons E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ▷ P ∗
    ∀ Q, ▷ (▷ Q ={∅}=∗ ▷ P) -∗ ▷ Q ={E}=∗ &{κ} Q ∗ q.[κ].
Proof.
  iIntros (?) "#LFT HP Htok".
  iMod (bor_acc_strong with "LFT HP Htok") as (κ') "(#Hκκ' & $ & Hclose)"; first done.
  iIntros "!>* HPQ HQ". iMod ("Hclose" with "[HPQ] HQ") as "[Hb $]".
  - iNext. iIntros "? _". by iApply "HPQ".
  - iApply (bor_shorten with "Hκκ' Hb").
Qed.

Lemma bor_acc E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
Proof.
  iIntros (?) "#LFT HP Htok".
  iMod (bor_acc_cons with "LFT HP Htok") as "($ & Hclose)"; first done.
  iIntros "!>HP". iMod ("Hclose" with "[] HP") as "[$ $]"; auto.
Qed.

Lemma bor_exists {A} (Φ : A → iProp Σ) `{!Inhabited A} E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}(Φ x).
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[H|[H† >_]]"; first done.
  - iDestruct "H" as "[HΦ Hclose]". iDestruct "HΦ" as (x) "HΦ".
    iExists x. iApply ("Hclose" with "[] HΦ"). iIntros "!> ?"; eauto.
  - iExists inhabitant. by iApply (bor_fake with "LFT").
Qed.

Lemma bor_or E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
Proof.
  iIntros (?) "#LFT H". rewrite bi.or_alt.
  (* The (A:=...) is needed due to Coq bug #5458 *)
  iMod (bor_exists (A:=bool) with "LFT H") as ([]) "H"; auto.
Qed.

Lemma bor_iff_proper κ P P': ▷ □ (P ↔ P') -∗ □ (&{κ}P ↔ &{κ}P').
Proof.
  iIntros "#HP !#". iSplit; iIntros "?"; iApply bor_iff; try done.
  iNext. iAlways. iSplit; iIntros "?"; iApply "HP"; done.
Qed.

Lemma bor_later E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(▷ P) ={E,E∖↑lftN}▷=∗ &{κ}P.
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[H|[H† Hclose]]"; first done.
  - iDestruct "H" as "[HP  Hclose]". iModIntro. iNext.
    iApply ("Hclose" with "[] HP"). by iIntros "!> $".
  - iIntros "!> !>". iMod "Hclose" as "_". by iApply (bor_fake with "LFT").
Qed.

Lemma bor_later_tok E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(▷ P) -∗ q.[κ] ={E}▷=∗ &{κ}P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose]"; first done.
  iModIntro. iNext. iApply ("Hclose" with "[] HP"). by iIntros "!> $".
Qed.

Lemma bor_persistent_notok P `{!Persistent P} E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P ={E}=∗ ▷ P ∨ [†κ].
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic with "LFT Hb") as "[[#HP Hob]|[#H† Hclose]]"; first done.
  - iMod ("Hob" with "HP") as "_". auto.
  - iMod "Hclose" as "_". auto.
Qed.

Lemma bor_persistent P `{!Persistent P} E κ q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc with "LFT Hb Htok") as "[#HP Hob]"; first done.
  by iMod ("Hob" with "HP") as "[_ $]".
Qed.

Lemma later_bor_static E P :
  ↑lftN ⊆ E →
  lft_ctx -∗ ▷ P ={E}=∗ &{static} P.
Proof.
  iIntros (?) "#LFT HP". iMod (bor_create with "LFT HP") as "[$ _]"; done.
Qed.

Lemma bor_static_later E P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{static} P ={E}=∗ ▷ P.
Proof.
  iIntros (?) "LFT HP". iMod (bor_acc _ 1%Qp with "LFT HP []") as "[$ _]"; try done.
  iApply lft_tok_static.
Qed.

Lemma rebor E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx -∗ κ' ⊑ κ -∗ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗ &{κ}P).
Proof.
  iIntros (?) "#LFT #Hκ'κ Hbor". rewrite [(&{κ}P)%I]bor_unfold_idx.
  iDestruct "Hbor" as (i) "[#Hbor Hidx]".
  iMod (bor_create _ κ' with "LFT Hidx") as "[Hidx Hinh]"; first done.
  iMod (idx_bor_unnest with "LFT Hbor Hidx") as "Hbor'"; first done.
  iDestruct (bor_shorten with "[] Hbor'") as "$".
  { iApply lft_incl_glb. done. iApply lft_incl_refl. }
  iIntros "!> H†". iMod ("Hinh" with "H†") as ">Hidx". auto with iFrame.
Qed.

Lemma bor_unnest E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ'} (&{κ} P) ={E}▷=∗ &{κ ⊓ κ'} P.
Proof.
  iIntros (?) "#LFT Hbor".
  rewrite ->(bor_unfold_idx _ P).
  iMod (bor_exists with "LFT Hbor") as (i) "Hbor"; [done|].
  iMod (bor_sep with "LFT Hbor") as "[Hidx Hbor]"; [done|].
  iMod (bor_persistent_notok with "LFT Hidx") as "#[Hidx|H†]"; [done| |].
  - iIntros "!>". iNext. by iApply (idx_bor_unnest with "LFT Hidx Hbor").
  - iApply (bor_fake with "LFT"); [done|]. rewrite -lft_dead_or. auto.
Qed.

Lemma lft_incl_static κ : (κ ⊑ static)%I.
Proof.
  iApply lft_incl_intro. iIntros "!#". iSplitR.
  - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_tok_static. auto.
  - iIntros "Hst". by iDestruct (lft_dead_static with "Hst") as "[]".
Qed.

Lemma lft_intersect_list_elem_of_incl κs κ :
  κ ∈ κs → (lft_intersect_list κs ⊑ κ)%I.
Proof.
  induction 1 as [|???? IH].
  - iApply lft_intersect_incl_l.
  - iApply lft_incl_trans; last iApply IH. (* FIXME: Why does "done" not do this? Looks like "assumption" to me. *)
    iApply lft_intersect_incl_r.
Qed.

Lemma lft_eternalize E q κ :
  q.[κ] ={E}=∗ static ⊑ κ.
Proof.
  iIntros "Hκ". iMod (inv_alloc lftN _ (∃ q, q.[κ])%I with "[Hκ]") as "#Hnv".
  { iExists _. done. }
  iApply lft_incl_intro. iIntros "!> !#". iSplitL.
  - iIntros (q') "$". iInv lftN as ">Hκ" "Hclose". iDestruct "Hκ" as (q'') "[Hκ1 Hκ2]".
    iMod ("Hclose" with "[Hκ2]") as "_". { iExists _. done. }
    iModIntro. iExists _. iFrame. iIntros "_". done.
  - iIntros "H†". iInv lftN as ">Hκ" "_". iDestruct "Hκ" as (q'') "Hκ".
    iDestruct (lft_tok_dead with "Hκ H†") as "[]".
Qed.

End derived.
