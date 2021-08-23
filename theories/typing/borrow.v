From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export uniq_bor shr_bor own.
From lrust.typing Require Import lft_contexts type_context programs.
From iris.prelude Require Import options.

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{!typeGS Σ}.

  Lemma tctx_borrow E L p n ty κ :
    tctx_incl E L [p ◁ own_ptr n ty] [p ◁ &uniq{κ}ty; p ◁{κ} own_ptr n ty].
  Proof.
    iIntros (tid ??)  "#LFT _ $ [H _]".
    iDestruct "H" as ([[]|]) "[% Hown]"; try done. iDestruct "Hown" as "[Hmt ?]".
    iMod (bor_create with "LFT Hmt") as "[Hbor Hext]"; first done.
    iModIntro. rewrite /tctx_interp /=. iSplitL "Hbor"; last iSplit; last done.
    - iExists _. auto.
    - iExists _. iSplit; first done. by iFrame.
  Qed.

  Lemma tctx_share E L p κ ty :
    lctx_lft_alive E L κ → tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &shr{κ}ty].
  Proof.
    iIntros (Hκ ???) "#LFT #HE HL Huniq".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; [try done..|].
    rewrite !tctx_interp_singleton /=.
    iDestruct "Huniq" as ([[]|]) "[% Huniq]"; try done.
    iMod (ty.(ty_share) with "LFT Huniq Htok") as "[Hown Htok]"; [solve_ndisj|].
    iMod ("Hclose" with "Htok") as "[$ $]". iExists _. by iFrame "%∗".
  Qed.

  (* When sharing during extraction, we do the (arbitrary) choice of
     sharing at the lifetime requested (κ). In some cases, we could
     actually desire a longer lifetime and then use subtyping, because
     then we get, in the environment, a shared borrow at this longer
     lifetime.

     In the case the user wants to do the sharing at a longer
     lifetime, she has to manually perform the extraction herself at
     the desired lifetime. *)
  Lemma tctx_extract_hasty_share E L p ty ty' κ κ' T :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' → subtype E L ty' ty →
    tctx_extract_hasty E L p (&shr{κ}ty) ((p ◁ &uniq{κ'}ty')::T)
                       ((p ◁ &shr{κ}ty')::(p ◁{κ} &uniq{κ'}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_;_]).
    rewrite tctx_reborrow_uniq //. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite tctx_share // {1}copy_tctx_incl.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, shr_mono'.
  Qed.

  Lemma tctx_extract_hasty_share_samelft E L p ty ty' κ T :
    lctx_lft_alive E L κ → subtype E L ty' ty →
    tctx_extract_hasty E L p (&shr{κ}ty) ((p ◁ &uniq{κ}ty')::T)
                                         ((p ◁ &shr{κ}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite tctx_share // {1}copy_tctx_incl.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, shr_mono'.
  Qed.

  Lemma tctx_extract_hasty_borrow E L p n ty ty' κ T :
    subtype E L ty' ty →
    tctx_extract_hasty E L p (&uniq{κ}ty) ((p ◁ own_ptr n ty')::T)
                       ((p ◁{κ} own_ptr n ty)::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]). rewrite subtype_tctx_incl.
    - by apply tctx_borrow.
    - by f_equiv.
  Qed.

  (* See the comment above [tctx_extract_hasty_share]. *)
  Lemma tctx_extract_hasty_borrow_share E L p ty ty' κ n T :
    lctx_lft_alive E L κ → subtype E L ty' ty →
    tctx_extract_hasty E L p (&shr{κ}ty) ((p ◁ own_ptr n ty')::T)
                       ((p ◁ &shr{κ}ty')::(p ◁{κ} own_ptr n ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_;_]). rewrite ->tctx_borrow.
    apply (tctx_incl_frame_r _ [_] [_;_]). rewrite ->tctx_share; solve_typing.
  Qed.

  Lemma type_deref_uniq_own_instr {E L} κ p n ty :
    lctx_lft_alive E L κ →
    ⊢ typed_instruction_ty E L [p ◁ &uniq{κ}(own_ptr n ty)] (!p) (&uniq{κ} ty).
  Proof.
    iIntros (Hκ tid qmax) "#LFT HE $ HL Hp".
    rewrite tctx_interp_singleton.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros ([[|l|]|]) "_ Hown"; try done.
    iMod (bor_acc_cons with "LFT Hown Htok") as "[H↦ Hclose']"; first done.
    iDestruct "H↦" as ([|[[|l'|]|][]]) "[>H↦ Hown]"; try iDestruct "Hown" as ">[]".
      iDestruct "Hown" as "[Hown H†]". rewrite heap_mapsto_vec_singleton -wp_fupd. wp_read.
    iMod ("Hclose'" $! (l↦#l' ∗ freeable_sz n (ty_size ty) l' ∗ _)%I
          with "[] [H↦ Hown H†]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]"; first done.
      iMod (bor_sep with "LFT Hbor") as "[_ Hbor]"; first done.
      iMod ("Hclose" with "Htok") as "HL".
      iDestruct ("HLclose" with "HL") as "$".
      by rewrite tctx_interp_singleton tctx_hasty_val' //=.
    - iIntros "!>(?&?&?)!>". iNext. iExists _.
      rewrite -heap_mapsto_vec_singleton. iFrame. by iFrame.
    - iFrame.
  Qed.

  Lemma type_deref_uniq_own {E L} κ x p e n ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&uniq{κ}(own_ptr n ty)) T T' →
    lctx_lft_alive E L κ →
    (∀ (v:val), typed_body E L C ((v ◁ &uniq{κ}ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_uniq_own_instr|solve_typing|done]. Qed.

  Lemma type_deref_shr_own_instr {E L} κ p n ty :
    lctx_lft_alive E L κ →
    ⊢ typed_instruction_ty E L [p ◁ &shr{κ}(own_ptr n ty)] (!p) (&shr{κ} ty).
  Proof.
    iIntros (Hκ tid qmax) "#LFT HE $ HL Hp".
    rewrite tctx_interp_singleton.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|]) "_ Hown"; try done.
    iDestruct "Hown" as (l') "#[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']"; first done.
    iApply (wp_step_fupd _ _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "[%] Htok2"); first solve_ndisj.
    - iApply wp_fupd. wp_read. iIntros "!>[#Hshr Htok2]".
      iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
      iMod ("Hclose" with "[Htok1 Htok2]") as "HL"; first by iFrame.
      iDestruct ("HLclose" with "HL") as "$".
      rewrite tctx_interp_singleton tctx_hasty_val' //. auto.
  Qed.

  Lemma type_deref_shr_own {E L} κ x p e n ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&shr{κ}(own_ptr n ty)) T T' →
    lctx_lft_alive E L κ →
    (∀ (v:val), typed_body E L C ((v ◁ &shr{κ} ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_shr_own_instr|solve_typing|done]. Qed.

  Lemma type_deref_uniq_uniq_instr {E L} κ κ' p ty :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    ⊢ typed_instruction_ty E L [p ◁ &uniq{κ}(&uniq{κ'}ty)] (!p) (&uniq{κ} ty).
  Proof.
    iIntros (Hκ Hincl tid qmax) "#LFT #HE $ HL Hp".
    rewrite tctx_interp_singleton.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iDestruct (Hincl with "HL HE") as "%".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|]) "_ Hown"; try done.
    iMod (bor_exists with "LFT Hown") as (vl) "Hbor"; first done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]"; first done.
    destruct vl as [|[[]|][]];
      try by iMod (bor_persistent with "LFT Hbor Htok") as "[>[] _]".
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']"; first done.
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_unnest with "LFT Hbor") as "Hbor"; [done|].
    iApply wp_fupd. wp_read.
    iMod ("Hclose'" with "[H↦]") as "[H↦ Htok]"; first by auto.
    iMod ("Hclose" with "Htok") as "HL".
    iDestruct ("HLclose" with "HL") as "$".
    rewrite tctx_interp_singleton tctx_hasty_val' //.
    iApply (bor_shorten with "[] Hbor").
    iApply lft_incl_glb; first by iApply lft_incl_syn_sem. iApply lft_incl_refl.
  Qed.

  Lemma type_deref_uniq_uniq {E L} κ κ' x p e ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&uniq{κ}(&uniq{κ'}ty))%T T T' →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀ (v:val), typed_body E L C ((v ◁ &uniq{κ}ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_uniq_uniq_instr|solve_typing|done]. Qed.

  Lemma type_deref_shr_uniq_instr {E L} κ κ' p ty :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    ⊢ typed_instruction_ty E L [p ◁ &shr{κ}(&uniq{κ'}ty)] (!p) (&shr{κ}ty).
  Proof.
    iIntros (Hκ Hincl tid qmax) "#LFT HE $ HL Hp". rewrite tctx_interp_singleton.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iDestruct (Hincl with "HL HE") as "%".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|]) "_ Hshr"; try done.
    iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']"; first done.
    iAssert (κ ⊑ κ' ⊓ κ)%I as "#Hincl'".
    { iApply lft_incl_glb.
      + by iApply lft_incl_syn_sem.
      + by iApply lft_incl_refl. }
    iMod (lft_incl_acc with "Hincl' Htok2") as (q2) "[Htok2 Hclose'']"; first solve_ndisj.
    iApply (wp_step_fupd _ _ (_∖_) with "[Hown Htok2]"); try done.
    { iApply ("Hown" with "[%] Htok2"); first solve_ndisj. }
    iApply wp_fupd. wp_read. iIntros "!>[#Hshr Htok2]".
    iMod ("Hclose''" with "Htok2") as "Htok2".
    iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
    iMod ("Hclose" with "[Htok1 Htok2]") as "HL"; first by iFrame.
    iDestruct ("HLclose" with "HL") as "$".
    rewrite tctx_interp_singleton tctx_hasty_val' //.
    by iApply (ty_shr_mono with "Hincl' Hshr").
  Qed.

  Lemma type_deref_shr_uniq {E L} κ κ' x p e ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&shr{κ}(&uniq{κ'}ty))%T T T' →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀ (v:val), typed_body E L C ((v ◁ &shr{κ}ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_shr_uniq_instr|solve_typing|done]. Qed.
End borrow.

Global Hint Resolve tctx_extract_hasty_borrow tctx_extract_hasty_borrow_share
               | 10 : lrust_typing.
Global Hint Resolve tctx_extract_hasty_share | 10 : lrust_typing.
Global Hint Resolve tctx_extract_hasty_share_samelft | 9 : lrust_typing.
