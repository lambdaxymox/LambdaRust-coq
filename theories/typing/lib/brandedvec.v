From iris.algebra Require Import auth numbers.
From iris.proofmode Require Import tactics.
From lrust.lang Require Import proofmode notation lib.new_delete.
From lrust.lifetime Require Import meta.
From lrust.typing Require Import typing.
From lrust.typing.lib Require Import option.
Set Default Proof Using "Type".

Definition brandidx_stR := max_natUR.
Class brandidxG Σ := BrandedIdxG {
  brandidx_inG :> inG Σ (authR brandidx_stR);
  brandidx_gsingletonG :> lft_metaG Σ;
}.

Definition brandidxΣ : gFunctors
  := #[GFunctor (authR brandidx_stR); lft_metaΣ].
Instance subG_brandidxΣ {Σ} : subG brandidxΣ Σ → brandidxG Σ.
Proof. solve_inG. Qed.

Definition brandidxN := lrustN .@ "brandix".
Definition brandvecN := lrustN .@ "brandvec".

Section brandedvec.
  Context `{!typeG Σ, !brandidxG Σ}.
  Implicit Types (q : Qp) (α : lft) (γ : gname) (n m : nat).
  Local Notation iProp := (iProp Σ).

  Definition brandvec_inv α n : iProp :=
    (∃ γ, lft_meta α γ ∗ own γ (● MaxNat n))%I.

  Program Definition brandvec (α : lft) : type :=
    {| ty_size        := int.(ty_size);
       ty_own tid vl  :=
        (∃ n, brandvec_inv α n ∗ ⌜vl = [ #n ]⌝)%I;
       ty_shr κ tid l :=
        (∃ n, &at{κ,brandvecN}(brandvec_inv α n) ∗ &frac{κ}(λ q, l ↦∗{q} [ #n ]))%I;
    |}.
  Next Obligation. iIntros "* H". iDestruct "H" as (?) "[_ %]". by subst. Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hown Hκ".
    iMod (bor_exists with "LFT Hown") as (vl) "Hown"; first solve_ndisj.
    iMod (bor_sep with "LFT Hown") as "[Hshr Hown]"; first solve_ndisj.
    iMod (bor_exists with "LFT Hown") as (n) "Hown"; first solve_ndisj.
    iMod (bor_sep with "LFT Hown") as "[Hghost Hown]"; first solve_ndisj.
    iMod (bor_share _ brandvecN with "Hghost") as "Hghost"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hown Hκ") as "[> % $]"; first solve_ndisj.
    subst. iExists n. iFrame.
    by iApply (bor_fracture with "LFT"); first solve_ndisj.
  Qed.
  Next Obligation.
    iIntros (ty ?? tid l) "#H⊑ H".
    iDestruct "H" as (n) "[Hghost Hown]".
    iExists n. iSplitR "Hown".
    - by iApply (at_bor_shorten with "H⊑").
    - by iApply (frac_bor_shorten with "H⊑").
  Qed.

  Global Instance brandvec_wf α : TyWf (brandvec α) :=
    { ty_lfts := [α]; ty_wf_E := [] }.
  Global Instance brandvec_ne : NonExpansive brandvec.
  Proof. solve_proper. Qed.
  Global Instance brandvec_mono E L :
    Proper (lctx_lft_eq E L ==> subtype E L) brandvec.
  Proof. apply lft_invariant_subtype. Qed.
  Global Instance brandvec_equiv E L :
    Proper (lctx_lft_eq E L ==> eqtype E L) brandvec.
  Proof. apply lft_invariant_eqtype. Qed.

  Global Instance brandvec_send α :
    Send (brandvec α).
  Proof. by unfold brandvec, Send. Qed.

  Global Instance brandvec_sync α :
    Sync (brandvec α).
  Proof. by unfold brandvec, Sync. Qed.

  (** [γ] is (a lower bound of) the length of the vector; as an in-bounds index,
  that must be at least one more than the index value. *)
  Definition brandidx_inv α m : iProp :=
    (∃ γ, lft_meta α γ ∗ own γ (◯ MaxNat (m+1)%nat))%I.

  Program Definition brandidx α :=
    {| ty_size        := int.(ty_size);
       ty_own tid vl  := (∃ m, brandidx_inv α m ∗ ⌜vl = [ #m]⌝)%I;
       ty_shr κ tid l := (∃ m, &frac{κ}(λ q, l ↦∗{q} [ #m]) ∗ brandidx_inv α m)%I;
    |}.
  Next Obligation. iIntros "* H". iDestruct "H" as (?) "[_ %]". by subst. Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hown Hκ".
    iMod (bor_exists with "LFT Hown") as (vl) "Hown"; first solve_ndisj.
    iMod (bor_sep with "LFT Hown") as "[Hown Hghost]"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hghost Hκ") as "[>Hghost $]"; first solve_ndisj.
    iDestruct "Hghost" as (m) "[Hghost %]". subst vl.
    iExists m. iFrame.
    by iApply (bor_fracture with "LFT"); first solve_ndisj.
  Qed.
  Next Obligation.
    iIntros (ty ?? tid l) "#H⊑ H".
    iDestruct "H" as (m) "[H ?]".
    iExists m. iFrame.
    by iApply (frac_bor_shorten with "H⊑").
  Qed.

  Global Instance brandidx_wf α : TyWf (brandidx α) :=
    { ty_lfts := [α]; ty_wf_E := [] }.
  Global Instance brandidx_ne : NonExpansive brandidx.
  Proof. solve_proper. Qed.
  Global Instance brandidx_mono E L :
    Proper (lctx_lft_eq E L ==> subtype E L) brandidx.
  Proof. apply lft_invariant_subtype. Qed.
  Global Instance brandidx_equiv E L :
    Proper (lctx_lft_eq E L ==> eqtype E L) brandidx.
  Proof. apply lft_invariant_eqtype. Qed.

  Global Instance brandidx_send α :
    Send (brandidx α).
  Proof. by unfold brandidx, Send. Qed.

  Global Instance brandidx_sync α :
    Sync (brandidx α).
  Proof. by unfold brandidx, Sync. Qed.

  Global Instance brandidx_copy α :
    Copy (brandidx α).
  Proof.
    split; first by apply _.
    iIntros (κ tid E ? l q ? HF) "#LFT #Hshr Htok Hlft".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iDestruct "Hshr" as (γ) "[Hmem Hinv]".
    iMod (frac_bor_acc with "LFT Hmem Hlft") as (q') "[>Hmt Hclose]"; first solve_ndisj.
    iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iModIntro. iExists _.
    iSplitL "Hmt1".
    { iExists [_]. iNext. iFrame. iExists _. eauto with iFrame. }
    iIntros "Htok2 Hmt1". iDestruct "Hmt1" as (vl') "[>Hmt1 #Hown']".
    iDestruct ("Htok" with "Htok2") as "$".
    iAssert (▷ ⌜1 = length vl'⌝)%I as ">%".
    { iNext. iDestruct (ty_size_eq with "Hown'") as %->. done. }
    destruct vl' as [|v' vl']; first done.
    destruct vl' as [|]; last first. { simpl in *. lia. }
    rewrite !heap_mapsto_vec_singleton.
    iDestruct (heap_mapsto_agree with "[$Hmt1 $Hmt2]") as %->.
    iCombine "Hmt1" "Hmt2" as "Hmt".
    iApply "Hclose". done.
  Qed.

  Lemma brandinv_brandidx_lb α m n :
    brandvec_inv α n -∗ brandidx_inv α m -∗ ⌜m < n⌝%nat.
  Proof.
    iIntros "Hn Hm".
    iDestruct "Hn" as (γn) "(Hidx1 & Hn)".
    iDestruct "Hm" as (γm) "(Hidx2 & Hm)".
    iDestruct (lft_meta_agree with "Hidx1 Hidx2") as %<-.
    iDestruct (own_valid_2 with "Hn Hm") as %[?%max_nat_included ?]%auth_both_valid_discrete.
    iPureIntro. simpl in *. lia.
  Qed.

End brandedvec.

Section typing.
  Context `{!typeG Σ, !brandidxG Σ}.
  Implicit Types (q : Qp) (α : lft) (γ : gname) (n m : nat).
  Local Notation iProp := (iProp Σ).

  Definition brandvec_new (call_once : val) (R_F : type) : val :=
    fn: ["f"] :=
      let: "call_once" := call_once in
      letalloc: "n" <- #0 in
      letcall: "r" := "call_once" ["f";"n"]%E in
      letalloc: "r'" <-{ R_F.(ty_size)} !"r" in
      delete [ #R_F.(ty_size); "r"];;
      return: ["r'"].

  Lemma brandvec_new_type F R_F call_once `{!TyWf F, !TyWf R_F} :
    typed_val call_once (fn(∀ α, ∅; F, brandvec α) → R_F) →
    typed_val (brandvec_new call_once R_F) (fn(∅; F) → R_F).
  Proof.
    iIntros (Hf E L). iApply type_fn; [solve_typing..|]. iIntros "/= !#".
    iIntros (_ ϝ ret args). inv_vec args=> env. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (f); simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hc (Hf & Henv & _)".
    wp_let.
    wp_op.
    wp_case.
    wp_alloc n as "Hn" "Hdead".
    wp_let.
    rewrite !heap_mapsto_vec_singleton.
    wp_write.
    iAssert (∀ E : coPset, ⌜↑lftN ⊆ E⌝ →
      |={E}=> ∃ α, tctx_elt_interp tid ((LitV n : expr) ◁ box (brandvec α)) ∗ 1.[α])%I
      with "[Hn Hdead]" as "Hn'".
    { iIntros (E' Hlft).
      iMod (own_alloc (● (MaxNat 0))) as (γ) "Hown"; first by apply auth_auth_valid.
      iMod (lft_create_meta γ with "LFT") as (α) "[#Hsing [Htok #Hα]]"; first done.
      iExists α.
      rewrite !tctx_hasty_val.
      rewrite ownptr_own.
      rewrite -heap_mapsto_vec_singleton.
      iFrame "Htok".
      iExists n, (Vector.cons (LitV 0) Vector.nil).
      iSplitR; first done.
      simpl.
      rewrite freeable_sz_full.
      iFrame.
      iExists 0%nat.
      iSplitL; last done.
      iExists γ; iSplitR; by eauto. }
    iMod ("Hn'" with "[%]") as (α) "[Hn Htok]"; [solve_typing..|].
    wp_let.
    iMod (lctx_lft_alive_tok ϝ with "HE HL")
      as (qϝf) "(Hϝf & HL & Hclosef)"; [solve_typing..|].

    iDestruct (lft_intersect_acc with "Htok Hϝf") as (?) "[Hαϝ Hcloseα]".
    rewrite !tctx_hasty_val.
    iApply (type_call_iris _ [α; ϝ] α [_;_]  _ _ _ _
              with "LFT HE Hna [Hαϝ] Hf [Hn Henv]"); try solve_typing.
    + by rewrite /= right_id.
    + rewrite /= right_id.
      rewrite !tctx_hasty_val.
      by iFrame.
    + iIntros (r) "Hna Hf Hown".
      simpl_subst.
      iDestruct ("Hcloseα" with "[Hf]") as "[Htok Hf]"; first by rewrite right_id.
      iMod ("Hclosef" with "Hf HL") as "HL".
      wp_let.
      iApply (type_type _ _ _ [ r ◁ box R_F ] with "[] LFT HE Hna HL Hc");
        try solve_typing; last by rewrite !tctx_interp_singleton tctx_hasty_val.
      iApply type_letalloc_n; [solve_typing..|].
      iIntros (r').
      simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition brandvec_get_index : val :=
    fn: ["v"; "i"] :=
      let: "r" := new [ #2 ] in
      let: "v'" := !"v" in
      let: "i'" := !"i" in
      delete [ #1; "v" ];; delete [ #1; "i" ];;
      let: "inbounds" := (if: #0 ≤ "i'" then "i'" < !"v'" else #false) in
      if: "inbounds" then
        "r" <-{Σ some} "i'";;
         return: ["r"]
      else
        "r" <-{Σ none} ();;
        return: ["r"].

  Lemma brandvec_get_index_type :
    typed_val brandvec_get_index (fn(∀ '(α, β), ∅; &shr{β} (brandvec α), int) → option (brandidx α))%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
    iIntros ([α β] ϝ ret args). inv_vec args=>v i. simpl_subst.
    iApply (type_new 2); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (v'); simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (i'); simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iIntros (tid qmax) "#LFT #HE Hna HL Hk (#Hi' & #Hv' & Hr & _)".
    rewrite !tctx_hasty_val. clear.
    destruct i' as [[| |i']|]; try done. iClear "Hi'".
    wp_op.
    rewrite bool_decide_decide.
    destruct (decide (0 ≤ i')) as [Hpos|Hneg]; last first.
    { wp_case. wp_let. wp_case.
      iApply (type_type _ _ _ [ r ◁ box (uninit 2) ]
            with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_singleton tctx_hasty_val. done. }
      iApply (type_sum_unit (option (brandidx _))); [solve_typing..|].
      iApply type_jump; solve_typing. }
    destruct (Z_of_nat_complete _ Hpos) as [i ->]. clear Hpos.
    wp_case. wp_op.
    iDestruct (shr_is_ptr with "Hv'") as % [l ?]. simplify_eq.
    iDestruct "Hv'" as (m) "#[Hghost Hmem]".
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hmem Hβ") as (qβ') "[>Hn'↦ Hcloseβ]"; first done.
    rewrite !heap_mapsto_vec_singleton.
    wp_read.
    iMod ("Hcloseβ" with "Hn'↦") as "Hβ".
    wp_op.
    rewrite bool_decide_decide.
    destruct (decide (i + 1 ≤ m)) as [Hle|Hoob]; last first.
    { wp_let. wp_case.
      iMod ("Hclose" with "Hβ HL") as "HL".
      iApply (type_type _ _ _ [ r ◁ box (uninit 2) ]
            with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_singleton tctx_hasty_val. done. }
      iApply (type_sum_unit (option (brandidx _))); [solve_typing..|].
      iApply type_jump; solve_typing. }
    wp_let. wp_case.
    iApply fupd_wp.
    iMod (at_bor_acc_tok with "LFT Hghost Hβ") as "[>Hidx Hcloseg]"; [solve_ndisj..|].
    iDestruct "Hidx" as (γ) "(#Hidx & Hown)".
    iAssert (|==> own γ (● (MaxNat m)) ∗ own γ (◯ (MaxNat m)))%I with "[Hown]" as "> [Hown Hlb]".
    { rewrite -own_op. iApply (own_update with "Hown"). apply auth_update_alloc.
      by apply max_nat_local_update. }
    iMod ("Hcloseg" with "[Hown]") as "Hβ".
    { iExists _. eauto with iFrame. }
    iMod ("Hclose" with "Hβ HL") as "HL".
    iApply (type_type _ _ _ [ r ◁ box (uninit 2); #i ◁ brandidx _ ]
            with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val'; last done.
        iExists _. iSplit; last done.
        iExists _. iFrame "Hidx".
        iApply base_logic.lib.own.own_mono; last done.
        apply: auth_frag_mono. apply max_nat_included. simpl. lia. }
    iApply (type_sum_assign (option (brandidx _))); [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition brandidx_get : val :=
    fn: ["s";"c"] :=
      let: "len" := !"s" in
      let: "idx" := !"c" in
      delete [ #1; "s" ];; delete [ #1; "c" ];;
      if: !"idx" < !"len" then
        let: "r" := new [ #0] in return: ["r"]
      else
        !#☠ (* stuck *).

  Lemma brandidx_get_type :
    typed_val brandidx_get (fn(∀ '(α, β), ∅; &shr{β} (brandvec α), &shr{β} (brandidx α)) → unit)%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
    iIntros ([α β] ϝ ret args). inv_vec args=> s c. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (n); simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (m); simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iIntros (tid qmax) "#LFT #HE Hna HL HC (Hm & Hn & _)".
    rewrite !tctx_hasty_val.
    iDestruct (shr_is_ptr with "Hm") as %[lm ?]. simplify_eq.
    iDestruct (shr_is_ptr with "Hn") as %[ln ?]. simplify_eq.
    simpl in *.
    iDestruct "Hm" as (m) "[Hm Hmidx]".
    iDestruct "Hn" as (n) "[Hnidx Hn]".
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "((Hβ1 & Hβ2 & Hβ3) & HL & Hclose)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hn Hβ1") as (qβn) "[>Hn↦ Hcloseβ1]"; first solve_ndisj.
    iMod (frac_bor_acc with "LFT Hm Hβ2") as (qβm) "[>Hm↦ Hcloseβ2]"; first solve_ndisj.
    rewrite !heap_mapsto_vec_singleton.
    wp_read.
    wp_op.
    wp_read.
    wp_op.
    wp_case.
    iApply fupd_wp.
    iMod (at_bor_acc_tok with "LFT Hnidx Hβ3") as "[>Hnidx Hcloseβ3]"; [solve_ndisj..|].
    iDestruct (brandinv_brandidx_lb with "Hnidx Hmidx") as %Hle.
    iMod ("Hcloseβ3" with "Hnidx") as "Hβ3".
    iMod ("Hcloseβ2" with "Hm↦") as "Hβ2".
    iMod ("Hcloseβ1" with "Hn↦") as "Hβ1".
    iCombine "Hβ2 Hβ3" as "Hβ2".
    iMod ("Hclose" with "[$Hβ1 $Hβ2] HL") as "HL".
    rewrite bool_decide_true; last by lia.
    iApply (type_type _ _ _ []
            with "[] LFT HE Hna HL HC []"); last by rewrite tctx_interp_nil.
    iApply (type_new _); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  Definition brandvec_push : val :=
    fn: ["s"] :=
      let: "n" := !"s" in
      delete [ #1; "s" ];;
      let: "r" := new [ #1] in
      let: "oldlen" := !"n" in
      "n" <- "oldlen"+#1;;
      "r" <- "oldlen";;
      return: ["r"].

  Lemma brandvec_push_type :
    typed_val brandvec_push (fn(∀ '(α, β), ∅; &uniq{β} (brandvec α)) → brandidx α).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
    iIntros ([α β] ϝ ret args). inv_vec args=>(*n *)s. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (n); simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply (type_new _); [solve_typing..|]; iIntros (r); simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL HC (Hr & Hn & _)".
    rewrite !tctx_hasty_val.
    iDestruct (uniq_is_ptr with "Hn") as %[ln H]. simplify_eq.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose)"; [solve_typing..|].
    iMod (bor_acc with "LFT Hn Hβ") as "[H↦ Hclose']"; first solve_ndisj.
    iDestruct "H↦" as (vl) "[> H↦ Hn]".
    iDestruct "Hn" as (n) "[Hn > %]". simplify_eq.
    rewrite !heap_mapsto_vec_singleton.
    wp_read.
    wp_let.
    wp_op.
    wp_write.
    iDestruct "Hn" as (γ) "[#Hidx Hown]".
    iMod (own_update _ _ (● MaxNat (n+1) ⋅ _) with "Hown") as "[Hown Hlb]".
    { apply auth_update_alloc.
      apply max_nat_local_update.
      simpl. lia.
    }
    iDestruct "Hlb" as "#Hlb".
    iMod ("Hclose'" with "[H↦ Hidx Hown]") as "[Hn Hβ]".
    { iExists (#(n+1)::nil).
      rewrite heap_mapsto_vec_singleton.
      iFrame "∗".
      iIntros "!>".
      iExists (n + 1)%nat.
      iSplitL; last by (iPureIntro; do 3 f_equal; lia).
      iExists γ. eauto with iFrame.
    }
    iMod ("Hclose" with "Hβ HL") as "HL".
    iApply (type_type _ _ _ [ r ◁ box (uninit 1); #n ◁ brandidx _]
            with "[] LFT HE Hna HL HC [Hr]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val. iFrame.
      rewrite tctx_hasty_val'; last done.
      iExists _. iSplit; last done.
      iExists _. eauto with iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End typing.
