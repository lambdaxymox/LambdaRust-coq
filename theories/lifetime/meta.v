From iris.algebra Require Import dyn_reservation_map agree.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Export lifetime.
Set Default Proof Using "Type".

(** This module provides support for attaching metadata (specifically, a
[gname]) to a lifetime (as is required for types using branding). *)

Class lft_metaG Σ := LftMetaG {
  lft_meta_inG :> inG Σ (dyn_reservation_mapR (agreeR gnameO));
}.
Definition lft_metaΣ : gFunctors :=
  #[GFunctor (dyn_reservation_mapR (agreeR gnameO))].
Instance subG_lft_meta Σ :
  subG (lft_metaΣ) Σ → lft_metaG Σ.
Proof. solve_inG. Qed.

(** We need some global ghost state, but we do not actually care about the name:
we always use a frame-preserving update starting from ε to obtain the ownership
we need. In other words, we use [own_unit] instead of [own_alloc]. As a result
we can just hard-code an arbitrary name here. *)
Local Definition lft_meta_gname : gname := 42%positive.

Definition lft_meta `{!lftG Σ, lft_metaG Σ} (κ : lft) (γ : gname) : iProp Σ :=
  ∃ p : positive, ⌜κ = positive_to_lft p⌝ ∗
    own lft_meta_gname (dyn_reservation_map_data p (to_agree γ)).

Section lft_meta.
  Context `{!invG Σ, !lftG Σ, lft_metaG Σ}.

  Global Instance lft_meta_timeless κ γ : Timeless (lft_meta κ γ).
  Proof. apply _. Qed.
  Global Instance lft_meta_persistent κ γ : Persistent (lft_meta κ γ).
  Proof. apply _. Qed.

  Lemma lft_create_meta {E : coPset} (γ : gname) :
    ↑lftN ⊆ E →
    lft_ctx ={E}=∗
    ∃ κ, lft_meta κ γ ∗ (1).[κ] ∗ □ ((1).[κ] ={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=∗ [†κ]).
  Proof.
    iIntros (HE) "#LFT".
    iMod (own_unit (dyn_reservation_mapUR (agreeR gnameO)) lft_meta_gname) as "Hown".
    iMod (own_updateP _ _ _ dyn_reservation_map_reserve' with "Hown")
      as (? [Etok [Hinf ->]]) "Hown".
    iMod (lft_create_strong (.∈ Etok) with "LFT") as (p HEtok) "Hκ"; [done..|].
    iExists (positive_to_lft p). iFrame "Hκ".
    iMod (own_update with "Hown") as "Hown".
    { eapply (dyn_reservation_map_alloc _ p (to_agree γ)); done. }
    iModIntro. iExists p. eauto.
  Qed.

  Lemma lft_meta_agree (κ : lft) (γ1 γ2 : gname) :
    lft_meta κ γ1 -∗ lft_meta κ γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    iIntros "Hidx1 Hidx2".
    iDestruct "Hidx1" as (p1) "(% & Hidx1)". subst κ.
    iDestruct "Hidx2" as (p2) "(Hlft & Hidx2)".
    iDestruct "Hlft" as %<-%(inj positive_to_lft).
    iCombine "Hidx1 Hidx2" as "Hidx".
    iDestruct (own_valid with "Hidx") as %Hval.
    rewrite ->(dyn_reservation_map_data_valid (A:=agreeR gnameO)) in Hval.
    apply to_agree_op_inv_L in Hval.
    done.
  Qed.
End lft_meta.

Typeclasses Opaque lft_meta.
