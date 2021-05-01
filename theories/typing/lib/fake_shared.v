From iris.proofmode Require Import tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section fake_shared.
  Context `{!typeG Σ}.

  Definition fake_shared_box : val :=
    fn: ["x"] := Skip ;; return: ["x"].

  Lemma fake_shared_box_type ty `{!TyWf ty} :
    typed_val fake_shared_box
      (fn(∀ '(α, β), ∅; &shr{α}(&shr{β} ty)) → &shr{α}(box ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hk HT".
    rewrite tctx_interp_singleton tctx_hasty_val.
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "%"; [solve_typing..|].
    iAssert (▷ ty_own (own_ptr 1 (&shr{α}(box ty))) tid [x])%I with "[HT]" as "HT".
    { destruct x as [[|l|]|]=>//=. iDestruct "HT" as "[H $]".
      iNext. iDestruct "H" as ([|[[]|][]]) "[H↦ H]"; try done.
      iExists _. iFrame. iDestruct "H" as (vl) "[#Hf H]".
      iNext. destruct vl as [|[[|l'|]|][]]; try done. iExists l'. iSplit.
      { iApply frac_bor_iff; last done. iIntros "!>!# *".
        rewrite heap_mapsto_vec_singleton. iSplit; auto. }
      iDestruct "H" as "#H". iIntros "!# * % $". iApply step_fupd_intro. set_solver.
      simpl. iApply ty_shr_mono; last done.
      by iApply lft_incl_syn_sem. }
    do 2 wp_seq.
    iApply (type_type [] _ _ [ x ◁ box (&shr{α}(box ty)) ]
            with "[] LFT [] Hna HL Hk [HT]"); last first.
    { by rewrite tctx_interp_singleton tctx_hasty_val. }
    { by rewrite /elctx_interp. }
    iApply type_jump; simpl; solve_typing.
  Qed.

  Definition fake_shared_uniq : val :=
    fn: ["x"] := Skip ;; return: ["x"].

  Lemma fake_shared_uniq_type ty `{!TyWf ty} :
    typed_val fake_shared_box
      (fn(∀ '(α, β), ∅; &shr{α}(&shr{β} ty)) → &shr{α}(&uniq{β} ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hk HT".
    rewrite tctx_interp_singleton tctx_hasty_val.
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "%"; [solve_typing..|].
    (* FIXME: WTF, using &uniq{β} here does not work. *)
    iAssert (▷ ty_own (own_ptr 1 (&shr{α} (uniq_bor β ty))) tid [x])%I with "[HT]" as "HT".
    { destruct x as [[|l|]|]=>//=. iDestruct "HT" as "[H $]".
      iNext. iDestruct "H" as ([|[[]|][]]) "[H↦ H]"; try done.
      iExists _. iFrame. iDestruct "H" as (vl) "[#Hf H]".
      iNext. destruct vl as [|[[|l'|]|][]]; try done. iExists l'. iSplit.
      { iApply frac_bor_iff; last done. iIntros "!>!# *".
        rewrite heap_mapsto_vec_singleton. iSplit; auto. }
      iDestruct "H" as "#H". iIntros "!# * % $". iApply step_fupd_intro. set_solver.
      simpl. iApply ty_shr_mono; last done.
      by iApply lft_intersect_incl_l.
    }
    do 2 wp_seq.
    iApply (type_type [] _ _ [ x ◁ box (&shr{α}(&uniq{β} ty)) ]
            with "[] LFT [] Hna HL Hk [HT]"); last first.
    { by rewrite tctx_interp_singleton tctx_hasty_val. }
    { by rewrite /elctx_interp. }
    iApply type_jump; simpl; solve_typing.
  Qed.
End fake_shared.
