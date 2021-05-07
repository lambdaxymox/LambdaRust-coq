From iris.proofmode Require Import tactics.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition joinN := lrustN .@ "join".

Section join.
  Context `{!typeG Σ, !spawnG Σ}.

  (* This model is very far from rayon::join, which uses a persistent
     work-stealing thread-pool.  Still, the important bits are right:
     One of the closures is executed in another thread, and the
     closures can refer to on-stack data (no 'static' bound). *)
  Definition join (call_once_A call_once_B : val) (R_A R_B : type) : val :=
    fn: ["fA"; "fB"] :=
      let: "call_once_A" := call_once_A in
      let: "call_once_B" := call_once_B in
      let: "join" := spawn [λ: ["c"],
                            letcall: "r" := "call_once_A" ["fA"]%E in
                            finish ["c"; "r"]] in
      letcall: "retB" := "call_once_B" ["fB"]%E in
      let: "retA" := spawn.join ["join"] in
      (* Put the results in a pair. *)
      let: "ret" := new [ #(R_A.(ty_size) + R_B.(ty_size)) ] in
      "ret" +ₗ #0 <-{R_A.(ty_size)} !"retA";;
      "ret" +ₗ #R_A.(ty_size) <-{R_B.(ty_size)} !"retB";;
      delete [ #R_A.(ty_size); "retA"] ;; delete [ #R_B.(ty_size); "retB"] ;;
      return: ["ret"].

  Lemma join_type A B R_A R_B call_once_A call_once_B
        `{!TyWf A, !TyWf B, !TyWf R_A, !TyWf R_B}
        `(!Send A, !Send B, !Send R_A, !Send R_B) :
    (* A : FnOnce() -> R_A, as witnessed by the impl call_once_A *)
    typed_val call_once_A (fn(∅; A) → R_A) →
    (* B : FnOnce() -> R_B, as witnessed by the impl call_once_B *)
    typed_val call_once_B (fn(∅; B) → R_B) →
    typed_val (join call_once_A call_once_B R_A R_B) (fn(∅; A, B) → Π[R_A; R_B]).
  Proof using Type*.
    intros HfA HfB E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>envA envB. simpl_subst.
    iApply type_let; [apply HfA|solve_typing|]. iIntros (fA); simpl_subst.
    iApply type_let; [apply HfB|solve_typing|]. iIntros (fB); simpl_subst.
    (* Drop to Iris. *)
    iIntros (tid qmax) "#LFT #HE Hna HL Hk (HfB & HfA & HenvA & HenvB & _)".
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (qϝ1) "(Hϝ1 & HL & Hclose1)";
      [solve_typing..|].
    (* FIXME: using wp_apply here breaks calling solve_to_val. *)
    wp_bind (spawn _).
    iApply ((spawn_spec joinN (λ v, (box R_A).(ty_own) tid [v] ∗ (qϝ1).[ϝ])%I) with "[HfA HenvA Hϝ1]").
    { (* The new thread. *)
      simpl_subst. iIntros (c) "Hfin". iMod na_alloc as (tid') "Htl". wp_let.
      wp_let. unlock. rewrite !tctx_hasty_val.
      iApply (type_call_iris _ [ϝ] () [_] with "LFT HE Htl [Hϝ1] HfA [HenvA]").
      - rewrite outlives_product. solve_typing.
      - by rewrite /= (right_id static).
      - by rewrite big_sepL_singleton tctx_hasty_val send_change_tid.
      - iIntros (r) "Htl Hϝ1 Hret".
        wp_rec. iApply (finish_spec with "[$Hfin Hret Hϝ1]"); last auto.
        rewrite right_id. iFrame. by iApply @send_change_tid. }
    iNext. iIntros (c) "Hjoin". wp_let. wp_let.
    iMod (lctx_lft_alive_tok_noend ϝ with "HE HL") as (qϝ2) "(Hϝ2 & HL & Hclose2)";
      [solve_typing..|].
    rewrite !tctx_hasty_val.
    iApply (type_call_iris _ [ϝ] () [_] with "LFT HE Hna [Hϝ2] HfB [HenvB]").
    { rewrite outlives_product. solve_typing. }
    { by rewrite /= (right_id static). }
    { by rewrite big_sepL_singleton tctx_hasty_val. }
    (* The return continuation after calling fB in the main thread. *)
    iIntros (retB) "Hna Hϝ2 HretB". rewrite /= (right_id static).
    iMod ("Hclose2" with "Hϝ2 HL") as "HL". wp_rec.
    wp_apply (join_spec with "Hjoin"). iIntros (retA) "[HretA Hϝ1]".
    iMod ("Hclose1" with "Hϝ1 HL") as "HL". wp_let.
    (* Switch back to type system mode. *)
    iApply (type_type _ _ _ [ retA ◁ box R_A; retB ◁ box R_B ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
    iApply (type_new_subtype (Π[uninit R_A.(ty_size); uninit R_B.(ty_size)]));
      (* FIXME: solve_typing should handle this without any aid. *)
      rewrite ?Z_nat_add; [solve_typing..|].
    iIntros (r); simpl_subst.
    iApply (type_memcpy R_A); [solve_typing..|].
    iApply (type_memcpy R_B); [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End join.
