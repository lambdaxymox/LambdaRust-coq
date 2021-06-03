From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import tactics.
From lrust.lang Require Import races adequacy proofmode notation.
From lrust.lifetime Require Import lifetime frac_borrow.
From lrust.typing Require Import typing.

Set Default Proof Using "Type".

Class typeGpreS Σ := PreTypeG {
  type_preG_lrustGS :> lrustGpreS Σ;
  type_preG_lftGS :> lftGpreS Σ;
  type_preG_na_invG :> na_invG Σ;
  type_preG_frac_borG :> frac_borG Σ
}.

Definition typeΣ : gFunctors :=
  #[lrustΣ; lftΣ; na_invΣ; GFunctor (constRF fracR)].
Instance subG_typeGpreS {Σ} : subG typeΣ Σ → typeGpreS Σ.
Proof. solve_inG. Qed.

Section type_soundness.
  Definition exit_cont : val := λ: [<>], #☠.

  Definition main_type `{!typeGS Σ} := (fn(∅) → unit)%T.

  Theorem type_soundness `{!typeGpreS Σ} (main : val) σ t :
    (∀ `{!typeGS Σ}, typed_val main main_type) →
    rtc erased_step ([main [exit_cont]%E], ∅) (t, σ) →
    nonracing_threadpool t σ ∧
    (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
  Proof.
    intros Hmain Hrtc.
    cut (adequate NotStuck (main [exit_cont]%E) ∅ (λ _ _, True)).
    { split. by eapply adequate_nonracing.
      intros. by eapply (adequate_not_stuck _ (main [exit_cont]%E)). }
    apply: lrust_adequacy=>?. iIntros "_".
    iMod (lft_init _ lft_userE) as (?) "#LFT"; [done|solve_ndisj|].
    iMod na_alloc as (tid) "Htl". set (Htype := TypeG _ _ _ _ _).
    wp_bind (of_val main). iApply (wp_wand with "[Htl]").
    iApply (Hmain Htype [] [] $! tid 1%Qp with "LFT [] Htl [] []").
    { by rewrite /elctx_interp big_sepL_nil. }
    { by rewrite /llctx_interp big_sepL_nil. }
    { by rewrite tctx_interp_nil. }
    clear Hrtc Hmain main. iIntros (main) "(Htl & _ & Hmain & _)".
    iDestruct "Hmain" as (?) "[EQ Hmain]".
    rewrite eval_path_of_val. iDestruct "EQ" as %[= <-].
    iDestruct "Hmain" as (f k x e ?) "(EQ & % & Hmain)". iDestruct "EQ" as %[= ->].
    destruct x; try done. wp_rec.
    iMod (lft_create with "LFT") as (ϝ) "Hϝ"; first done.
    iApply ("Hmain" $! () ϝ exit_cont [#] tid 1%Qp with "LFT [] Htl [Hϝ] []");
      last by rewrite tctx_interp_nil.
    { by rewrite /elctx_interp /=. }
    { rewrite /llctx_interp /=. iSplit; last done. iExists ϝ.
      rewrite /= left_id. iSplit; first done.
      rewrite decide_True //.
      by iDestruct "Hϝ" as "[$ #$]". }
    rewrite cctx_interp_singleton. simpl. iIntros (args) "_ _".
    inv_vec args. iIntros (x) "_ /=". by wp_lam.
  Qed.
End type_soundness.

(* Soundness theorem when no other CMRA is needed. *)

Theorem type_soundness_closed (main : val) σ t :
  (∀ `{!typeGS typeΣ}, typed_val main main_type) →
  rtc erased_step ([main [exit_cont]%E], ∅) (t, σ) →
  nonracing_threadpool t σ ∧
  (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
Proof.
  intros. eapply @type_soundness; try done. apply _.
Qed.
