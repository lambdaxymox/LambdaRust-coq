From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section diverging_static.
  Context `{!typeG Σ}.

  (* Show that we can convert any live borrow to 'static with an infinite
     loop. *)
  Definition diverging_static_loop (call_once : val) : val :=
    fn: ["x"; "f"] :=
      let: "call_once" := call_once in
      letcall: "ret" := "call_once" ["f"; "x"]%E in
    withcont: "loop":
      "loop" []
    cont: "loop" [] :=
      "loop" [].

  Lemma diverging_static_loop_type T F call_once
        `{!TyWf T, !TyWf F} :
    (* F : FnOnce(&'static T), as witnessed by the impl call_once *)
    typed_val call_once (fn(∅; F, &shr{static} T) → unit) →
    typed_val (diverging_static_loop call_once)
              (fn(∀ α, λ ϝ, ty_outlives_E T static; &shr{α} T, F) → ∅).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x f. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (call); simpl_subst.
    (* Drop to Iris *)
    iIntros (tid qmax) "#LFT #HE Hna HL Hk (Hcall & Hx & Hf & _)".
    (* We need a ϝ token to show that we can call F despite it being non-'static. *)
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (qϝ) "(Hϝ & HL & _)";
      [solve_typing..|].
    iMod (lctx_lft_alive_tok_noend α with "HE HL") as (q) "(Hα & _ & _)";
      [solve_typing..|].
    iMod (lft_eternalize with "Hα") as "#Hα".
    iAssert (type_incl (box (&shr{α} T)) (box (&shr{static} T))) as "#[_ [Hincl _]]".
    { iApply box_type_incl. iNext. iApply shr_type_incl; first done.
      iApply type_incl_refl. }
    wp_let. rewrite tctx_hasty_val.
    iApply (type_call_iris _ [ϝ] () [_; _] with "LFT HE Hna [Hϝ] Hcall [Hx Hf]").
    - solve_typing.
    - by rewrite /= (right_id static).
    - simpl. iFrame. iSplit; last done. rewrite !tctx_hasty_val.
      iApply "Hincl". done.
    - iClear "Hα Hincl". iIntros (r) "Htl Hϝ1 Hret". wp_rec.
      (* Go back to the type system. *)
      iApply (type_type _ [] _ [] with "[] LFT HE Htl [] Hk [-]"); last first.
      { rewrite /tctx_interp /=. done. }
      { rewrite /llctx_interp /=. done. }
      iApply (type_cont [] [] (λ _, [])).
      + iIntros (?). simpl_subst. iApply type_jump; solve_typing.
      + iIntros "!>" (? args). inv_vec args. simpl_subst. iApply type_jump; solve_typing.
  Qed.


  (** With the right typing rule, we can prove a variant of the above where the
      lifetime is in an arbitrary invariant position, without even leaving the
      type system.  This is incompatible with branding!

      Our [TyWf] is not working well for type constructors (we have no way of
      representing the fact that well-formedness is somewhat "uniform"), so we
      instead work with a constant [Euser] of lifetime inclusion assumptions (in
      general it could change with the type parameter but only in monotone ways)
      and a single [κuser] of lifetimes that have to be alive (making κuser a
      list would require some induction-based reasoning principles that we do
      not have, but showing that it works for one lifetime is enough to
      demonstrate the principle). *)
  Lemma diverging_static_loop_type_bad (T : lft → type) F κuser Euser call_once
        `{!TyWf F} :
    (* The "bad" type_equivalize_lft_static rule *)
    (∀ E L C T κ e,
      (⊢ typed_body ((static ⊑ₑ κ) :: E) L C T e) →
      ⊢ typed_body E ((κ ⊑ₗ []) :: L) C T e) →
    (* Typing of this function *)
    let _ : (∀ κ, TyWf (T κ)) := λ κ, {| ty_lfts := [κ; κuser]; ty_wf_E := Euser |} in
    (∀ κ1 κ2, (T κ1).(ty_size) = (T κ2).(ty_size)) →
    (∀ E L κ1 κ2, lctx_lft_eq E L κ1 κ2 → subtype E L (T κ1) (T κ2)) →
    typed_val call_once (fn(∅; F, T static) → unit) →
    typed_val (diverging_static_loop call_once)
              (fn(∀ α, ∅; T α, F) → ∅).
  Proof.
    intros type_equivalize_lft_static_bad HWf HTsz HTsub Hf E L.
    iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x f. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (call); simpl_subst.
    iApply (type_cont [_] [] (λ r, [(r!!!0%fin:val) ◁ box (unit)])).
    { iIntros (k). simpl_subst.
      iApply type_equivalize_lft_static_bad.
      iApply (type_call [ϝ] ()); solve_typing. }
    iIntros "!> *". inv_vec args=>r. simpl_subst.
    iApply (type_cont [] [] (λ r, [])).
    { iIntros (kloop). simpl_subst. iApply type_jump; solve_typing. }
    iIntros "!> *". inv_vec args. simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
End diverging_static.
