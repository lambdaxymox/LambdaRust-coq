From iris.proofmode Require Import tactics.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section product.
  Context `{!typeG Σ}.

  (* TODO: Find a better spot for this. *)
  Lemma Z_nat_add (n1 n2 : nat) : Z.to_nat (n1 + n2) = (n1 + n2)%nat.
  Proof. rewrite Z2Nat.inj_add; [|lia..]. rewrite !Nat2Z.id //. Qed.

  (* "Pre"-unit.  We later define the full unit as the empty product.  That's
     convertible, but products are opaque in some hint DBs, so this does make a
     difference. *)
  Program Definition unit0 : type :=
    {| ty_size := 0; ty_own tid vl := ⌜vl = []⌝%I; ty_shr κ tid l := True%I |}.
  Next Obligation. iIntros (tid vl) "%". by subst. Qed.
  Next Obligation. by iIntros (??????) "_ _ $". Qed.
  Next Obligation. by iIntros (????) "_ $". Qed.

  Global Instance unit0_copy : Copy unit0.
  Proof.
    split. by apply _. iIntros (????????) "_ _ Htok $".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iExists 1%Qp. iModIntro. iSplitR.
    { iExists []. iSplitL; last by auto. rewrite heap_mapsto_vec_nil. auto. }
    iIntros "Htok2 _". iApply "Htok". done.
  Qed.

  Global Instance unit0_send : Send unit0.
  Proof. iIntros (tid1 tid2 vl) "H". done. Qed.

  Global Instance unit0_sync : Sync unit0.
  Proof. iIntros (????) "_". done. Qed.

  Lemma split_prod_mt tid ty1 ty2 q l :
    (l ↦∗{q}: λ vl,
       ∃ vl1 vl2, ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I
       ⊣⊢ l ↦∗{q}: ty1.(ty_own) tid ∗ (l +ₗ ty1.(ty_size)) ↦∗{q}: ty2.(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app. iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %->.
      iSplitL "H1 H↦1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]". iDestruct "H1" as (vl1) "[H↦1 H1]".
      iDestruct "H2" as (vl2) "[H↦2 H2]". iExists (vl1 ++ vl2).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "H1") as %->.
      iFrame. iExists _, _. by iFrame.
  Qed.

  Program Definition product2 (ty1 ty2 : type) :=
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_own tid vl := (∃ vl1 vl2,
         ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I;
       ty_shr κ tid l :=
         (ty1.(ty_shr) κ tid l ∗
          ty2.(ty_shr) κ tid (l +ₗ ty1.(ty_size)))%I |}.
  Next Obligation.
    iIntros (ty1 ty2 tid vl) "H". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
    subst. rewrite app_length !ty_size_eq.
    iDestruct "H1" as %->. iDestruct "H2" as %->. done.
  Qed.
  Next Obligation.
    intros ty1 ty2 E κ l tid q ?. iIntros "#LFT /=H Htok". rewrite split_prod_mt.
    iMod (bor_sep with "LFT H") as "[H1 H2]"; first solve_ndisj.
    iMod (ty1.(ty_share) with "LFT H1 Htok") as "[? Htok]"; first solve_ndisj.
    iMod (ty2.(ty_share) with "LFT H2 Htok") as "[? Htok]"; first solve_ndisj.
    iModIntro. iFrame "Htok". iFrame.
  Qed.
  Next Obligation.
    intros ty1 ty2 κ κ' tid l. iIntros "/= #H⊑ [H1 H2]".
    iSplitL "H1"; by iApply (ty_shr_mono with "H⊑").
  Qed.

  Global Instance product2_type_ne n:
    Proper (type_dist2 n ==> type_dist2 n ==> type_dist2 n) product2.
  Proof. solve_type_proper. Qed.

  Global Instance product2_ne :
    NonExpansive2 product2.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance product2_mono E L:
    Proper (subtype E L ==> subtype E L ==> subtype E L) product2.
  Proof.
    iIntros (ty11 ty12 H1 ty21 ty22 H2). iIntros (qmax qL) "HL".
    iDestruct (H1 with "HL") as "#H1". iDestruct (H2 with "HL") as "#H2".
    iClear "∗". iIntros "!# #HE".
    iDestruct ("H1" with "HE") as "#(% & #Ho1 & #Hs1)". clear H1.
    iDestruct ("H2" with "HE") as "#(% & #Ho2 & #Hs2)". clear H2.
    iSplit; first by (iPureIntro; simpl; f_equal). iSplit; iModIntro.
    - iIntros (??) "H". iDestruct "H" as (vl1 vl2) "(% & Hown1 & Hown2)".
      iExists _, _. iSplit. done. iSplitL "Hown1".
      + by iApply "Ho1".
      + by iApply "Ho2".
    - iIntros (???) "#[Hshr1 Hshr2]". iSplit.
      + by iApply "Hs1".
      + rewrite -(_ : ty_size ty11 = ty_size ty12) //. by iApply "Hs2".
  Qed.
  Global Instance product2_proper E L:
    Proper (eqtype E L ==> eqtype E L ==> eqtype E L) product2.
  Proof. by intros ??[]??[]; split; apply product2_mono. Qed.

  Global Instance product2_copy `{!Copy ty1} `{!Copy ty2} :
    Copy (product2 ty1 ty2).
  Proof.
    split; first (intros; apply _).
    intros κ tid E F l q ? HF. iIntros "#LFT [H1 H2] Htl [Htok1 Htok2]".
    iMod (@copy_shr_acc with "LFT H1 Htl Htok1") as (q1) "(Htl & H1 & Hclose1)"; first solve_ndisj.
    { rewrite <-HF. apply shr_locsE_subseteq. simpl. clear. lia. }
    iMod (@copy_shr_acc with "LFT H2 Htl Htok2") as (q2) "(Htl & H2 & Hclose2)"; first solve_ndisj.
    { move: HF. rewrite /= -plus_assoc shr_locsE_shift.
      assert (shr_locsE l (ty_size ty1) ## shr_locsE (l +ₗ (ty_size ty1)) (ty_size ty2 + 1))
             by exact: shr_locsE_disj.
      set_solver. }
    iDestruct (na_own_acc with "Htl") as "[$ Htlclose]".
    { generalize (shr_locsE_shift l ty1.(ty_size) ty2.(ty_size)). simpl. set_solver+. }
    destruct (Qp_lower_bound q1 q2) as (qq & q'1 & q'2 & -> & ->). iExists qq.
    iDestruct "H1" as (vl1) "[H↦1 H1]". iDestruct "H2" as (vl2) "[H↦2 H2]".
    rewrite !split_prod_mt.
    iDestruct (ty_size_eq with "H1") as "#>%".
    iDestruct (ty_size_eq with "H2") as "#>%".
    iDestruct "H↦1" as "[H↦1 H↦1f]". iDestruct "H↦2" as "[H↦2 H↦2f]".
    iIntros "!>". iSplitL "H↦1 H1 H↦2 H2".
    - iNext. iSplitL "H↦1 H1". iExists vl1. by iFrame. iExists vl2. by iFrame.
    - iIntros "Htl [H1 H2]". iDestruct ("Htlclose" with "Htl") as "Htl".
      iDestruct "H1" as (vl1') "[H↦1 H1]". iDestruct "H2" as (vl2') "[H↦2 H2]".
      iDestruct (ty_size_eq with "H1") as "#>%".
      iDestruct (ty_size_eq with "H2") as "#>%".
      iCombine "H↦1" "H↦1f" as "H↦1". iCombine "H↦2" "H↦2f" as "H↦2".
      rewrite !heap_mapsto_vec_op; [|congruence..].
      iDestruct "H↦1" as "[_ H↦1]". iDestruct "H↦2" as "[_ H↦2]".
      iMod ("Hclose2" with "Htl [H2 H↦2]") as "[Htl $]". by iExists _; iFrame.
      iMod ("Hclose1" with "Htl [H1 H↦1]") as "[$$]". by iExists _; iFrame. done.
  Qed.

  Global Instance product2_send `{!Send ty1} `{!Send ty2} :
    Send (product2 ty1 ty2).
  Proof.
    iIntros (tid1 tid2 vl) "H". iDestruct "H" as (vl1 vl2) "(% & Hown1 & Hown2)".
    iExists _, _. iSplit; first done. iSplitL "Hown1"; by iApply @send_change_tid.
  Qed.

  Global Instance product2_sync `{!Sync ty1} `{!Sync ty2} :
    Sync (product2 ty1 ty2).
  Proof.
    iIntros (κ tid1 ti2 l) "[#Hshr1 #Hshr2]". iSplit; by iApply @sync_change_tid.
  Qed.

  Definition product := foldr product2 unit0.
  Definition unit := product [].

  Global Instance product_wf tyl `{!TyWfLst tyl} : TyWf (product tyl) :=
    { ty_lfts := tyl_lfts tyl; ty_wf_E := tyl_wf_E tyl }.

  Lemma outlives_product ty1 ty2 ϝ `{!TyWf ty1, !TyWf ty2} :
    ty_outlives_E (product [ty1; ty2]) ϝ = ty_outlives_E ty1 ϝ ++ ty_outlives_E ty2 ϝ.
  Proof. rewrite /product /ty_outlives_E /= fmap_app //. Qed.

  Global Instance product_type_ne n: Proper (Forall2 (type_dist2 n) ==> type_dist2 n) product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Global Instance product_ne : NonExpansive product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Global Instance product_mono E L:
    Proper (Forall2 (subtype E L) ==> subtype E L) product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Lemma product_mono' E L tyl1 tyl2 :
    Forall2 (subtype E L) tyl1 tyl2 → subtype E L (product tyl1) (product tyl2).
  Proof. apply product_mono. Qed.
  Global Instance product_proper E L:
    Proper (Forall2 (eqtype E L) ==> eqtype E L) product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Lemma product_proper' E L tyl1 tyl2 :
    Forall2 (eqtype E L) tyl1 tyl2 → eqtype E L (product tyl1) (product tyl2).
  Proof. apply product_proper. Qed.
  Global Instance product_copy tys : LstCopy tys → Copy (product tys).
  Proof. induction 1; apply _. Qed.
  Global Instance product_send tys : LstSend tys → Send (product tys).
  Proof. induction 1; apply _. Qed.
  Global Instance product_sync tys : LstSync tys → Sync (product tys).
  Proof. induction 1; apply _. Qed.

  Definition product_cons ty tyl :
    product (ty :: tyl) = product2 ty (product tyl) := eq_refl _.
  Definition product_nil :
    product [] = unit0 := eq_refl _.
End product.

Notation Π := product.

Section typing.
  Context `{!typeG Σ}.

  Global Instance prod2_assoc E L : Assoc (eqtype E L) product2.
  Proof.
    intros ???. apply eqtype_unfold. iIntros (??) "_ !# _".
    iSplit; first by rewrite /= assoc. iSplit; iIntros "!# *"; iSplit; iIntros "H".
    - iDestruct "H" as (vl1 vl') "(% & Ho1 & H)".
      iDestruct "H" as (vl2 vl3) "(% & Ho2 & Ho3)". subst.
      iExists _, _. iSplit. by rewrite assoc. iFrame. iExists _, _. by iFrame.
    - iDestruct "H" as (vl1 vl') "(% & H & Ho3)".
      iDestruct "H" as (vl2 vl3) "(% & Ho1 & Ho2)". subst.
      iExists _, _. iSplit. by rewrite -assoc. iFrame. iExists _, _. by iFrame.
    - iDestruct "H" as "(Hs1 & Hs2 & Hs3)". rewrite shift_loc_assoc_nat.
      by iFrame.
    - iDestruct "H" as "[[Hs1 Hs2] Hs3]". rewrite /= shift_loc_assoc_nat.
      by iFrame.
  Qed.

  Global Instance prod2_unit_leftid E L : LeftId (eqtype E L) unit product2.
  Proof.
    intros ty. apply eqtype_unfold. iIntros (??) "_ !# _". iSplit; first done.
    iSplit; iIntros "!# *"; iSplit; iIntros "H".
    - iDestruct "H" as (? ?) "(% & % & ?)". by subst.
    - iExists [], _. eauto.
    - iDestruct "H" as "(? & ?)". rewrite shift_loc_0.
      iApply ty_shr_mono; last done.
      iApply lft_incl_refl.
    - simpl. rewrite shift_loc_0. by iFrame.
  Qed.

  Global Instance prod2_unit_rightid E L : RightId (eqtype E L) unit product2.
  Proof.
    intros ty. apply eqtype_unfold. iIntros (??) "_ !# _".
    iSplit; first by rewrite /= -plus_n_O. iSplit; iIntros "!# *"; iSplit; iIntros "H".
    - iDestruct "H" as (? ?) "(% & ? & %)". subst. by rewrite app_nil_r.
    - iExists _, []. rewrite app_nil_r. eauto.
    - iDestruct "H" as "(? & _)". done.
    - simpl. iFrame.
  Qed.

  Lemma prod_flatten E L tyl1 tyl2 tyl3 :
    eqtype E L (Π(tyl1 ++ Π tyl2 :: tyl3)) (Π(tyl1 ++ tyl2 ++ tyl3)).
  Proof.
    unfold product. induction tyl1; simpl; last by f_equiv.
    induction tyl2. by rewrite left_id. by rewrite /= -assoc; f_equiv.
  Qed.

  Lemma prod_flatten_l E L tyl1 tyl2 :
    eqtype E L (Π(Π tyl1 :: tyl2)) (Π(tyl1 ++ tyl2)).
  Proof. apply (prod_flatten _ _ []). Qed.
  Lemma prod_flatten_r E L tyl1 tyl2 :
    eqtype E L (Π(tyl1 ++ [Π tyl2])) (Π(tyl1 ++ tyl2)).
  Proof. by rewrite (prod_flatten E L tyl1 tyl2 []) app_nil_r. Qed.
  Lemma prod_app E L tyl1 tyl2 :
    eqtype E L (Π[Π tyl1; Π tyl2]) (Π(tyl1 ++ tyl2)).
  Proof. by rewrite -prod_flatten_r -prod_flatten_l. Qed.

  Lemma ty_outlives_E_elctx_sat_product E L tyl {Wf : TyWfLst tyl} α:
    elctx_sat E L (tyl_outlives_E tyl α) →
    elctx_sat E L (ty_outlives_E (Π tyl) α).
  Proof.
    intro Hsat. eapply eq_ind; first done. clear Hsat. rewrite /ty_outlives_E /=.
    induction Wf as [|ty [] ?? IH]=>//=. rewrite IH fmap_app //.
  Qed.
End typing.

Arguments product : simpl never.
Hint Opaque product : lrust_typing lrust_typing_merge.
Hint Resolve product_mono' product_proper' ty_outlives_E_elctx_sat_product
  : lrust_typing.
