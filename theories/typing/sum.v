From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From iris.bi Require Import fractional.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section sum.
  Context `{!typeGS Σ}.

  (* We define the actual empty type as being the empty sum, so that it is
     convertible to it---and in particular, we can pattern-match on it
     (as in, pattern-match in the language of lambda-rust, not in Coq). *)
  Program Definition emp0 : type :=
    {| ty_size := 1%nat;
       ty_own tid vl := False%I;
       ty_shr κ tid l := False%I |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation.
    iIntros (E κ l tid ??) "#LFT Hown Htok".
    iMod (bor_acc with "LFT Hown Htok") as "[>H _]"; first done.
    iDestruct "H" as (?) "[_ []]".
  Qed.
  Next Obligation. iIntros (κ κ' tid l) "#Hord []". Qed.

  Definition is_pad i tyl (vl : list val) : iProp Σ :=
    ⌜((nth i tyl emp0).(ty_size) + length vl)%nat = (max_list_with ty_size tyl)⌝%I.

  Lemma split_sum_mt l tid q tyl :
    (l ↦∗{q}: λ vl,
         ∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                               ⌜length vl = S (max_list_with ty_size tyl)⌝ ∗
                               ty_own (nth i tyl emp0) tid vl')%I
    ⊣⊢ ∃ (i : nat), (l ↦{q} #i ∗
                     (l +ₗ (S $ (nth i tyl emp0).(ty_size))) ↦∗{q}: is_pad i tyl) ∗
                              (l +ₗ 1) ↦∗{q}: (nth i tyl emp0).(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl' vl'') "(% & % & Hown)".
      subst. iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      iDestruct (ty_size_eq with "Hown") as "#EQ". iDestruct "EQ" as %Hvl'.
      iDestruct (heap_mapsto_vec_app with "Hmt") as "[Hmt Htail]". iSplitL "Htail".
      + iExists vl''. rewrite (shift_loc_assoc_nat _ 1) Hvl'. iFrame. iPureIntro.
        rewrite -Hvl'. simpl in *. rewrite -app_length. congruence.
      + iExists vl'. by iFrame.
    - iDestruct "H" as (i) "[[Hmt1 Htail] Hown]".
      iDestruct "Hown" as (vl') "[Hmt2 Hown]". iDestruct "Htail" as (vl'') "[Hmt3 %]".
      iDestruct (ty_size_eq with "Hown") as "#EQ". iDestruct "EQ" as %Hvl'.
      iExists (#i::vl'++vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Hvl'.
      iFrame. iExists i, vl', vl''. iSplit; first done. iFrame. iPureIntro.
      simpl. f_equal. by rewrite app_length Hvl'.
  Qed.

  Program Definition sum (tyl : list type) :=
    {| ty_size := S (max_list_with ty_size tyl);
       ty_own tid vl :=
         (∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                                ⌜length vl = S (max_list_with ty_size tyl)⌝ ∗
                                (nth i tyl emp0).(ty_own) tid vl')%I;
       ty_shr κ tid l :=
         (∃ (i : nat),
           &frac{κ} (λ q, l ↦{q} #i ∗
                     (l +ₗ (S $ (nth i tyl emp0).(ty_size))) ↦∗{q}: is_pad i tyl) ∗
               (nth i tyl emp0).(ty_shr) κ tid (l +ₗ 1))%I
    |}.
  Next Obligation.
    iIntros (tyl tid vl) "Hown". iDestruct "Hown" as (i vl' vl'') "(%&%&_)".
    subst. done.
  Qed.
  Next Obligation.
    intros tyl E κ l tid. iIntros (??) "#LFT Hown Htok". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Hown") as (i) "Hown"; first solve_ndisj.
    iMod (bor_sep with "LFT Hown") as "[Hmt Hown]"; first solve_ndisj.
    iMod ((nth i tyl emp0).(ty_share) with "LFT Hown Htok") as "[#Hshr $]"; try done.
    iMod (bor_fracture with "LFT [Hmt]") as "H'"; first solve_ndisj; last eauto.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (tyl κ κ' tid l) "#Hord H".
    iDestruct "H" as (i) "[Hown0 Hown]". iExists i.
    iSplitL "Hown0".
    - by iApply (frac_bor_shorten with "Hord").
    - iApply ((nth i tyl emp0).(ty_shr_mono) with "Hord"); done.
  Qed.

  Global Instance sum_wf tyl `{!ListTyWf tyl} : TyWf (sum tyl) :=
    { ty_lfts := tyl_lfts tyl; ty_wf_E := tyl_wf_E tyl }.

  Global Instance sum_type_ne n : Proper (Forall2 (type_dist2 n) ==> type_dist2 n) sum.
  Proof.
    intros x y EQ.
    assert (EQmax : max_list_with ty_size x = max_list_with ty_size y).
    { induction EQ as [|???? EQ _ IH]=>//=.
      rewrite IH. f_equiv. apply EQ. }
    (* TODO: If we had the right lemma relating nth, (Forall2 R) and R, we should
       be able to make this more automatic. *)
    assert (EQnth :∀ i, type_dist2 n (nth i x emp0) (nth i y emp0)).
    { clear EQmax. induction EQ as [|???? EQ _ IH]=>-[|i] //=. }
    constructor; simpl.
    - by rewrite EQmax.
    - intros tid vl. destruct n as [|n]=> //=. rewrite /ty_own /= EQmax.
      solve_proper_core ltac:(fun _ => exact:EQnth || f_type_equiv || f_equiv).
    - intros κ tid l. unfold is_pad. rewrite EQmax.
      solve_proper_core ltac:(fun _ => exact:EQnth || f_type_equiv || f_equiv).
  Qed.

  Global Instance sum_ne : NonExpansive sum.
  Proof.
    intros n x y EQ.
    assert (EQmax : max_list_with ty_size x = max_list_with ty_size y).
    { induction EQ as [|???? EQ _ IH]=>//=.
      rewrite IH. f_equiv. apply EQ. }
    (* TODO: If we had the right lemma relating nth, (Forall2 R) and R, we should
       be able to make this more automatic. *)
    assert (EQnth :∀ i, type_dist n (nth i x emp0) (nth i y emp0)).
    { clear EQmax. induction EQ as [|???? EQ _ IH]=>-[|i] //=. }
    constructor; simpl.
    - by rewrite EQmax.
    - intros tid vl. rewrite EQmax.
      solve_proper_core ltac:(fun _ => exact:EQnth || f_equiv).
    - intros κ tid l. unfold is_pad. rewrite EQmax.
      solve_proper_core ltac:(fun _ => exact:EQnth || (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance sum_mono E L :
    Proper (Forall2 (subtype E L) ==> subtype E L) sum.
  Proof.
    iIntros (tyl1 tyl2 Htyl qmax qL) "HL".
    iAssert (□ (elctx_interp E -∗ ⌜max_list_with ty_size tyl1 = max_list_with ty_size tyl2⌝))%I with "[#]" as "#Hleq".
    { iInduction Htyl as [|???? Hsub] "IH".
      { iClear "∗". iIntros "!> _". done. }
      iDestruct (Hsub with "HL") as "#Hsub". iDestruct ("IH" with "HL") as "{IH} #IH".
      iModIntro. iIntros "#HE". iDestruct ("Hsub" with "HE") as "(% & _ & _)".
      iDestruct ("IH" with "HE") as %IH. iPureIntro. simpl. inversion_clear IH. by f_equal. }
    iDestruct (subtype_Forall2_llctx_noend with "HL") as "#Htyl"; first done.
    iClear "HL". iIntros "!> #HE".
    iDestruct ("Hleq" with "HE") as %Hleq. iSpecialize ("Htyl" with "HE"). iClear "Hleq HE".
    iAssert (∀ i, type_incl (nth i tyl1 emp0) (nth i tyl2 emp0))%I with "[#]" as "#Hty".
      { iIntros (i). edestruct (nth_lookup_or_length tyl1 i) as [Hl1|Hl]; last first.
        { rewrite nth_overflow // nth_overflow; first by iApply type_incl_refl.
          by erewrite <-Forall2_length. }
        edestruct @Forall2_lookup_l as (ty2 & Hl2 & _); [done..|].
        iDestruct (big_sepL_lookup with "Htyl") as "Hty".
        { rewrite lookup_zip_with. erewrite Hl1. simpl.
          rewrite Hl2 /=. done. }
        rewrite (nth_lookup_Some tyl2 _ _ ty2) //. }
    clear -Hleq. iClear "∗". iSplit; last iSplit.
    - simpl. by rewrite Hleq.
    - iModIntro. iIntros (tid vl) "H". iDestruct "H" as (i vl' vl'') "(% & % & Hown)".
      iExists i, vl', vl''. iSplit; first done.
      iSplit; first by rewrite -Hleq.
      iDestruct ("Hty" $! i) as "(_ & #Htyi & _)". by iApply "Htyi".
    - iModIntro. iIntros (κ tid l) "H". iDestruct "H" as (i) "(Hmt & Hshr)".
      iExists i. iSplitR "Hshr".
      + rewrite /is_pad -Hleq. iDestruct ("Hty" $! i) as "(Hlen & _)".
        iDestruct "Hlen" as %<-. done.
      + iDestruct ("Hty" $! i) as "(_ & _ & #Htyi)". by iApply "Htyi".
  Qed.
  Lemma sum_mono' E L tyl1 tyl2 :
    Forall2 (subtype E L) tyl1 tyl2 → subtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_mono. Qed.
  Global Instance sum_proper E L :
    Proper (Forall2 (eqtype E L) ==> eqtype E L) sum.
  Proof.
    intros tyl1 tyl2 Heq; split; eapply sum_mono; [|rewrite -Forall2_flip];
      (eapply Forall2_impl; [done|by intros ?? []]).
  Qed.
  Lemma sum_proper' E L tyl1 tyl2 :
    Forall2 (eqtype E L) tyl1 tyl2 → eqtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_proper. Qed.

  Lemma nth_empty {A : Type} i (d : A) :
    nth i [] d = d.
  Proof. by destruct i. Qed.

  Global Instance sum_copy tyl : ListCopy tyl → Copy (sum tyl).
  Proof.
    intros HFA. split.
    - intros tid vl.
      cut (∀ i vl', Persistent (ty_own (nth i tyl emp0) tid vl')). by apply _.
      intros. apply @copy_persistent.
      edestruct nth_in_or_default as [| ->]; [by eapply List.Forall_forall| ].
      split; first by apply _. iIntros (????????) "? []".
    - intros κ tid E F l q ? HF.
      iIntros "#LFT #H Htl [Htok1 Htok2]".
      setoid_rewrite split_sum_mt. iDestruct "H" as (i) "[Hshr0 Hshr]".
      iMod (frac_bor_acc with "LFT Hshr0 Htok1") as (q'1) "[>Hown Hclose]"; first solve_ndisj.
      iAssert ((∃ vl, is_pad i tyl vl)%I) with "[#]" as %[vl Hpad].
      { iDestruct "Hown" as "[_ Hpad]". iDestruct "Hpad" as (vl) "[_ %]".
        eauto. }
      iMod (@copy_shr_acc _ _ (nth i tyl emp0) with "LFT Hshr Htl Htok2")
        as (q'2) "(Htl & HownC & Hclose')"; try done.
      { edestruct nth_in_or_default as [| ->]; first by eapply List.Forall_forall.
        split; first by apply _. iIntros (????????) "? []". }
      { rewrite <-HF. simpl. rewrite <-union_subseteq_r.
        apply shr_locsE_subseteq. lia. }
      iDestruct (na_own_acc with "Htl") as "[$ Htlclose]".
      { apply difference_mono_l.
        trans (shr_locsE (l +ₗ 1) (max_list_with ty_size tyl)).
        - apply shr_locsE_subseteq. lia.
        - set_solver+. }
      destruct (Qp_lower_bound q'1 q'2) as (q' & q'01 & q'02 & -> & ->).
      rewrite -(heap_mapsto_pred_op _ q' q'02); last (by intros; apply ty_size_eq).
      rewrite (fractional (Φ := λ q, _ ↦{q} _ ∗ _ ↦∗{q}: _)%I).
      iDestruct "HownC" as "[HownC1 HownC2]". iDestruct "Hown" as "[Hown1 Hown2]".
      iExists q'. iModIntro. iSplitL "Hown1 HownC1".
      + iNext. iExists i. iFrame.
      + iIntros "Htl H". iDestruct "H" as (i') "[>Hown1 HownC1]".
        iDestruct ("Htlclose" with "Htl") as "Htl".
        iDestruct (heap_mapsto_agree with "[Hown1 Hown2]") as "#Heq".
        { iDestruct "Hown1" as "[$ _]". iDestruct "Hown2" as "[$ _]". }
        iDestruct "Heq" as %[= ->%Z_of_nat_inj].
        iMod ("Hclose'" with "Htl [$HownC1 $HownC2]") as "[$ ?]".
        iMod ("Hclose" with "[$Hown1 $Hown2]") as "$". by iFrame.
  Qed.

  Global Instance sum_send tyl : ListSend tyl → Send (sum tyl).
  Proof.
    iIntros (Hsend tid1 tid2 vl) "H". iDestruct "H" as (i vl' vl'') "(% & % & Hown)".
    iExists _, _, _. iSplit; first done. iSplit; first done. iApply @send_change_tid; last done.
    edestruct nth_in_or_default as [| ->]; first by eapply List.Forall_forall.
    iIntros (???) "[]".
  Qed.

  Global Instance sum_sync tyl : ListSync tyl → Sync (sum tyl).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H". iDestruct "H" as (i) "[Hframe Hown]".
    iExists _. iFrame "Hframe". iApply @sync_change_tid; last done.
    edestruct nth_in_or_default as [| ->]; first by eapply List.Forall_forall.
    iIntros (????) "[]".
  Qed.

  Definition emp_type := sum [].

  Global Instance emp_type_empty : Empty type := emp_type.
End sum.

(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1%T (..(cons tyn%T nil)..))) : lrust_type_scope.

Global Hint Opaque sum : lrust_typing lrust_typing_merge.
Global Hint Resolve sum_mono' sum_proper' : lrust_typing.
