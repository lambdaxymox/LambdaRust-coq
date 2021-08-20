From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
Set Default Proof Using "Type".

Definition mutexN := lrustN .@ "mutex".

Section mutex.
  Context `{!typeGS Σ}.

  (*
    pub struct Mutex<T: ?Sized> {
      // Note that this mutex is in a *box*, not inlined into the struct itself.
      // Once a native mutex has been used once, its address can never change (it
      // can't be moved). This mutex type can be safely moved at any time, so to
      // ensure that the native mutex is used correctly we box the inner lock to
      // give it a constant address.
      inner: Box<sys::Mutex>,
      poison: poison::Flag,
      data: UnsafeCell<T>,
    }
  *)

  Program Definition mutex (ty : type) :=
    {| ty_size := 1 + ty.(ty_size);
       ty_own tid vl :=
         match vl return _ with
         | #(LitInt z) :: vl' =>
           ⌜∃ b, z = Z_of_bool b⌝ ∗ ty.(ty_own) tid vl'
         | _ => False end;
       ty_shr κ tid l := ∃ κ', κ ⊑ κ' ∗
           &at{κ, mutexN} (lock_proto l (&{κ'}((l +ₗ 1) ↦∗: ty.(ty_own) tid)))
    |}%I.
  Next Obligation.
    iIntros (??[|[[]|]]); try iIntros "[]". rewrite ty_size_eq.
    iIntros "[_ %] !% /=". congruence.
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hbor Htok".
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[H Hclose]"; first done.
    iDestruct "H" as ([|[[| |n]|]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    rewrite heap_mapsto_vec_cons. iDestruct "H↦" as ">[Hl H↦]".
    iDestruct "H" as "[>EQ Hown]". iDestruct "EQ" as %[b ->].
    (* We need to turn the ohne borrow into two, so we close it -- and then
       we open one of them again. *)
    iMod ("Hclose" $! ((∃ b, l ↦ #(Z_of_bool b)) ∗ ((l +ₗ 1) ↦∗: ty_own ty tid))%I
          with "[] [Hl H↦ Hown]") as "[Hbor Htok]".
    { clear. iNext. iIntros "[Hl Hown] !>". iNext. iDestruct "Hl" as (b) "Hl".
      iDestruct "Hown" as (vl) "[H↦ Hown]". iExists (#(Z_of_bool b) :: vl).
      rewrite heap_mapsto_vec_cons. iFrame. iPureIntro. eauto. }
    { iNext. iSplitL "Hl"; first by eauto.
      iExists vl. iFrame. }
    clear b vl. iMod (bor_sep with "LFT Hbor") as "[Hl Hbor]"; first done.
    iMod (bor_acc_cons with "LFT Hl Htok") as "[>Hl Hclose]"; first done.
    iDestruct "Hl" as (b) "Hl".
    iMod (lock_proto_create with "Hl [Hbor]") as "Hproto".
    { destruct b; last by iExact "Hbor". done. }
    iMod ("Hclose" with "[] Hproto") as "[Hl Htok]".
    { clear b. iIntros "!> Hproto !>".
      iDestruct (lock_proto_destroy with "Hproto") as (b) "[Hl _]".
      eauto 10 with iFrame. }
    iFrame "Htok". iExists κ.
    iMod (bor_share with "Hl") as "$"; [solve_ndisj..|].
    iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H".
    iDestruct "H" as (κ'') "(#Hlft & #Hlck)".
    iExists _. by iSplit; [iApply lft_incl_trans|iApply at_bor_shorten].
  Qed.

  Global Instance mutex_wf ty `{!TyWf ty} : TyWf (mutex ty) :=
    { ty_lfts := ty_lfts ty; ty_wf_E := ty_wf_E ty }.

  Global Instance mutex_type_ne : TypeNonExpansive mutex.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S ||
                                              f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance mutex_ne : NonExpansive mutex.
  Proof.
    constructor; solve_proper_core ltac:(fun _ => (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance mutex_mono E L : Proper (eqtype E L ==> subtype E L) mutex.
  Proof.
    move=>ty1 ty2 /eqtype_unfold EQ. iIntros (??) "HL".
    iDestruct (EQ with "HL") as "#EQ". iIntros "!> #HE". clear EQ.
    iDestruct ("EQ" with "HE") as "(% & #Howni & _) {EQ}".
    iSplit; last iSplit.
    - simpl. iPureIntro. f_equiv. done.
    - iIntros "!> %tid %vl Hvl". destruct vl as [|[[| |n]|]vl]; try done.
      simpl. iDestruct "Hvl" as "[$ Hvl]". by iApply "Howni".
    - iIntros "!> %κ %tid %l Hshr". iDestruct "Hshr" as (κ') "[Hincl Hshr]".
      iExists _. iFrame "Hincl". iApply (at_bor_iff with "[] Hshr"). iNext.
      iApply lock_proto_iff_proper. iApply bor_iff_proper. iNext.
      iApply heap_mapsto_pred_iff_proper.
      iModIntro; iIntros; iSplit; iIntros; by iApply "Howni".
  Qed.

  Global Instance mutex_proper E L :
    Proper (eqtype E L ==> eqtype E L) mutex.
  Proof. by split; apply mutex_mono. Qed.

  Global Instance mutex_send ty :
    Send ty → Send (mutex ty).
  Proof.
    iIntros (??? [|[[| |n]|]vl]); try done. iIntros "[$ Hvl]".
    by iApply send_change_tid.
  Qed.

  Global Instance mutex_sync ty :
    Send ty → Sync (mutex ty).
  Proof.
    iIntros (???? l) "Hshr". iDestruct "Hshr" as (κ') "[Hincl Hshr]".
    iExists _. iFrame "Hincl". iApply (at_bor_iff with "[] Hshr"). iNext.
    iApply lock_proto_iff_proper. iApply bor_iff_proper. iNext.
    iApply heap_mapsto_pred_iff_proper.
    iModIntro; iIntros; iSplit; iIntros; by iApply send_change_tid.
  Qed.
End mutex.

Section code.
  Context `{!typeGS Σ}.

  Definition mutex_new ty : val :=
    fn: ["x"] :=
      let: "m" := new [ #(mutex ty).(ty_size) ] in
      "m" +ₗ #1 <-{ty.(ty_size)} !"x";;
      mklock_unlocked ["m" +ₗ #0];;
      delete [ #ty.(ty_size); "x"];; return: ["m"].

  Lemma mutex_new_type ty `{!TyWf ty} :
    typed_val (mutex_new ty) (fn(∅; ty) → mutex ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    (* FIXME: It should be possible to infer the `S ty.(ty_size)` here.
       This should be done in the @eq external hints added in lft_contexts.v. *)
    iApply (type_new (S ty.(ty_size))); [solve_typing..|]; iIntros (m); simpl_subst.
    (* FIXME: The following should work.  We could then go into Iris later.
    iApply (type_memcpy ty); [solve_typing..|]. *)
    (* Switch to Iris. *)
    iIntros (tid qmax) "#LFT #HE Hna HL Hk [Hm [Hx _]]".
    rewrite !tctx_hasty_val /=.
    iDestruct (ownptr_uninit_own with "Hm") as (lm vlm) "(% & Hm & Hm†)".
    subst m. inv_vec vlm=>m vlm. simpl. iDestruct (heap_mapsto_vec_cons with "Hm") as "[Hm0 Hm]".
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct (heap_mapsto_ty_own with "Hx") as (vl) "[>Hx Hxown]".
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. wp_apply (wp_memcpy with "[$Hm $Hx]"); [by rewrite vec_to_list_length..|].
    iIntros "[Hm Hx]". wp_seq. wp_op. rewrite shift_loc_0. wp_lam.
    wp_write.
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ #lx ◁ box (uninit ty.(ty_size)); #lm ◁ box (mutex ty)]
        with "[] LFT HE Hna HL Hk"); last first.
    (* TODO: It would be nice to say [{#}] as the last spec pattern to clear the context in there. *)
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val' // tctx_hasty_val' //.
      iFrame. iSplitL "Hx".
      - iExists _. iFrame. by rewrite uninit_own vec_to_list_length.
      - iExists (#false :: vl). rewrite heap_mapsto_vec_cons. iFrame; eauto. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition mutex_into_inner ty : val :=
    fn: ["m"] :=
      let: "x" := new [ #ty.(ty_size) ] in
      "x" <-{ty.(ty_size)} !("m" +ₗ #1);;
      delete [ #(mutex ty).(ty_size); "m"];; return: ["x"].

  Lemma mutex_into_inner_type ty `{!TyWf ty} :
    typed_val (mutex_into_inner ty) (fn(∅; mutex ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>m. simpl_subst.
    iApply (type_new ty.(ty_size)); [solve_typing..|]; iIntros (x); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid qmax) "#LFT #HE Hna HL Hk [Hx [Hm _]]".
    rewrite !tctx_hasty_val /=.
    iDestruct (ownptr_uninit_own with "Hx") as (lx vlx) "(% & Hx & Hx†)".
    subst x. simpl.
    destruct m as [[|lm|]|]; try done. iDestruct "Hm" as "[Hm Hm†]".
    iDestruct (heap_mapsto_ty_own with "Hm") as (vlm) "[>Hm Hvlm]".
    inv_vec vlm=>m vlm. destruct m as [[|m|]|]; try by iDestruct "Hvlm" as ">[]".
    simpl. iDestruct (heap_mapsto_vec_cons with "Hm") as "[Hm0 Hm]".
    iDestruct "Hvlm" as "[_ Hvlm]".
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. wp_apply (wp_memcpy with "[$Hx $Hm]"); [by rewrite vec_to_list_length..|].
    (* FIXME: Swapping the order of $Hx and $Hm breaks. *)
    iIntros "[Hx Hm]". wp_seq.
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ #lx ◁ box ty; #lm ◁ box (uninit (mutex ty).(ty_size))]
        with "[] LFT HE Hna HL Hk"); last first.
    (* TODO: It would be nice to say [{#}] as the last spec pattern to clear the context in there. *)
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val' // tctx_hasty_val' //.
      iFrame. iSplitR "Hm0 Hm".
      - iExists _. iFrame.
      - iExists (_ :: _). rewrite heap_mapsto_vec_cons. iFrame.
        rewrite uninit_own. rewrite /= vec_to_list_length. eauto. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition mutex_get_mut : val :=
    fn: ["m"] :=
      let: "m'" := !"m" in
      "m" <- ("m'" +ₗ #1);;
      return: ["m"].

  Lemma mutex_get_mut_type ty `{!TyWf ty} :
    typed_val mutex_get_mut (fn(∀ α, ∅; &uniq{α}(mutex ty)) → &uniq{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg); inv_vec arg=>m; simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (m'); simpl_subst.
    (* Go to Iris *)
    iIntros (tid qmax) "#LFT #HE Hna HL Hk [Hm [Hm' _]]".
    rewrite !tctx_hasty_val [[m]]lock.
    destruct m' as [[|lm'|]|]; try done. simpl.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose1)";
      [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hm' Hα") as "[Hm' Hclose2]"; first done.
    wp_op. iDestruct "Hm'" as (vl) "[H↦ Hm']".
    destruct vl as [|[[|m'|]|] vl]; try done. simpl.
    iDestruct (heap_mapsto_vec_cons with "H↦") as "[H↦1 H↦2]".
    iDestruct "Hm'" as "[% Hvl]".
    iMod ("Hclose2" $! ((lm' +ₗ 1) ↦∗: ty_own ty tid)%I with "[H↦1] [H↦2 Hvl]") as "[Hbor Hα]".
    { iIntros "!> Hlm' !>". iNext. clear vl. iDestruct "Hlm'" as (vl) "[H↦ Hlm']".
      iExists (_ :: _). rewrite heap_mapsto_vec_cons. do 2 iFrame. done. }
    { iExists vl. iFrame. }
    iMod ("Hclose1" with "Hα HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ m ◁ own_ptr _ _; #(lm' +ₗ 1) ◁ &uniq{α} ty]
        with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End code.
