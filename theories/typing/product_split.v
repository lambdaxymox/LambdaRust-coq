From iris.algebra Require Import numbers.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context lft_contexts product own uniq_bor shr_bor.
Set Default Proof Using "Type".

Section product_split.
  Context `{!typeG Σ}.

  (** General splitting / merging for pointer types *)
  Fixpoint hasty_ptr_offsets (p : path) (ptr: type → type) tyl (off : nat) : tctx :=
    match tyl with
    | [] => []
    | ty :: tyl =>
      (p +ₗ #off ◁ ptr ty) :: hasty_ptr_offsets p ptr tyl (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_offset (l : loc) p (off1 off2 : nat) ptr tyl tid :
    eval_path p = Some #l →
    tctx_interp tid $ hasty_ptr_offsets (p +ₗ #off1) ptr tyl off2 ≡
    tctx_interp tid $ hasty_ptr_offsets p ptr tyl (off1 + off2)%nat.
  Proof.
    intros Hp.
    revert off1 off2; induction tyl; intros off1 off2; simpl; first done.
    rewrite !tctx_interp_cons. f_equiv; last first.
    { by rewrite IHtyl assoc_L. }
    apply tctx_elt_interp_hasty_path. clear Hp. simpl.
    clear. destruct (eval_path p); last done. destruct v; try done.
    destruct l; try done. rewrite shift_loc_assoc Nat2Z.inj_add //.
  Qed.

  Lemma tctx_split_ptr_prod E L ptr tyl :
    (∀ p ty1 ty2,
        tctx_incl E L [p ◁ ptr $ product2 ty1 ty2]
                      [p ◁ ptr ty1; p +ₗ #ty1.(ty_size) ◁ ptr ty2]) →
    (∀ tid ty vl, (ptr ty).(ty_own) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝) →
    ∀ p, tctx_incl E L [p ◁ ptr $ product tyl] (hasty_ptr_offsets p ptr tyl 0).
  Proof.
    iIntros (Hsplit Hloc p tid qmax qL) "#LFT #HE HL H".
    iInduction tyl as [|ty tyl IH] "IH" forall (p).
    { rewrite tctx_interp_nil. auto. }
    rewrite product_cons. iMod (Hsplit with "LFT HE HL H") as "(HL & H)".
    cbn -[tctx_elt_interp].
    iDestruct "H" as "[Hty Htyl]". iDestruct "Hty" as (v) "[Hp Hty]". iDestruct "Hp" as %Hp.
    iDestruct (Hloc with "Hty") as %[l [=->]].
    iAssert (tctx_elt_interp tid (p +ₗ #0 ◁ ptr ty)) with "[Hty]" as "$".
    { iExists #l. iSplit; last done. simpl; by rewrite Hp shift_loc_0. }
    iMod ("IH" with "HL [Htyl]") as "($ & Htyl)".
    { auto. }
    iClear "IH". rewrite (hasty_ptr_offsets_offset l) // -plus_n_O //.
  Qed.

  Lemma tctx_merge_ptr_prod E L ptr tyl :
    (Proper (eqtype E L ==> eqtype E L ) ptr) → tyl ≠ [] →
    (∀ p ty1 ty2,
        tctx_incl E L [p ◁ ptr ty1; p +ₗ #ty1.(ty_size) ◁ ptr ty2]
                      [p ◁ ptr $ product2 ty1 ty2]) →
    (∀ tid ty vl, (ptr ty).(ty_own) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝) →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p ptr tyl 0) [p ◁ ptr $ product tyl].
  Proof.
    iIntros (Hptr Htyl Hmerge Hloc p tid qmax qL) "#LFT #HE HL H".
    iInduction tyl as [|ty tyl IH] "IH" forall (p Htyl); first done.
    rewrite product_cons. rewrite /= tctx_interp_singleton tctx_interp_cons.
    iDestruct "H" as "[Hty Htyl]". iDestruct "Hty" as (v) "[Hp Hty]".
    iDestruct "Hp" as %Hp. iDestruct (Hloc with "Hty") as %[l [=->]].
    assert (eval_path p = Some #l) as Hp'.
    { move:Hp. simpl. clear. destruct (eval_path p); last done.
      destruct v; try done. destruct l0; try done. rewrite shift_loc_0. done. }
    clear Hp. destruct tyl.
    { assert (eqtype E L (ptr ty) (ptr (product2 ty unit))) as [Hincl _].
      { rewrite right_id. done. }
      iDestruct (Hincl with "HL HE") as "#(_ & #Heq & _)".
      iFrame. iClear "IH Htyl". iExists #l. rewrite product_nil. iSplitR; first done.
      by iApply "Heq". }
    iMod ("IH" with "[] HL [Htyl]") as "(HL & Htyl)"; first done.
    { change (ty_size ty) with (0+ty_size ty)%nat at 1.
      rewrite plus_comm -hasty_ptr_offsets_offset //. }
    iClear "IH". iMod (Hmerge with "LFT HE HL [Hty Htyl]") as "($ & ?)";
                   last by rewrite tctx_interp_singleton.
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton. iFrame.
    iExists #l. iSplit; done.
  Qed.

  (** Owned pointers *)
  Lemma tctx_split_own_prod2 E L p n ty1 ty2 :
    tctx_incl E L [p ◁ own_ptr n $ product2 ty1 ty2]
                  [p ◁ own_ptr n ty1; p +ₗ #ty1.(ty_size) ◁ own_ptr n ty2].
  Proof.
    iIntros (tid qmax qL) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|]) "[#Hp H]"; try done.
    iDestruct "H" as "[H >H†]". iDestruct "H" as (vl) "[>H↦ H]".
    iDestruct "H" as (vl1 vl2) "(>% & H1 & H2)". subst.
    rewrite heap_mapsto_vec_app -freeable_sz_split.
    iDestruct "H†" as "[H†1 H†2]". iDestruct "H↦" as "[H↦1 H↦2]".
    iDestruct (ty_size_eq with "H1") as "#>EQ".
    iDestruct "EQ" as %->. iSplitL "H↦1 H†1 H1".
    + iExists _. iFrame "#∗". iExists _. by iFrame.
    + iExists _. iSplitR; first (by simpl; iDestruct "Hp" as %->).
      iFrame. iExists _. by iFrame.
  Qed.

  Lemma tctx_merge_own_prod2 E L p n ty1 ty2 :
    tctx_incl E L [p ◁ own_ptr n ty1; p +ₗ #ty1.(ty_size) ◁ own_ptr n ty2]
                  [p ◁ own_ptr n $ product2 ty1 ty2].
  Proof.
    iIntros (tid qmax qL) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]". iDestruct "H1" as ([[]|]) "(Hp1 & H1)"; try done.
    iDestruct "H1" as "(H↦1 & H†1)".
    iDestruct "H2" as (v2) "(Hp2 & H2)". simpl. iDestruct "Hp1" as %Hρ1.
    rewrite Hρ1. iDestruct "Hp2" as %[=<-]. iDestruct "H2" as "[H↦2 H†2]".
    iExists #l. iSplitR; first done. rewrite /= -freeable_sz_split. iFrame.
    iDestruct "H↦1" as (vl1) "[H↦1 H1]". iDestruct "H↦2" as (vl2) "[H↦2 H2]".
    iExists (vl1 ++ vl2). rewrite heap_mapsto_vec_app. iFrame.
    iDestruct (ty_size_eq with "H1") as "#>EQ". iDestruct "EQ" as %->.
    rewrite {3}/ty_own /=. auto 10 with iFrame.
  Qed.

  Lemma tctx_split_own_prod E L n tyl p :
    tctx_incl E L [p ◁ own_ptr n $ product tyl] (hasty_ptr_offsets p (own_ptr n) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_own_prod2.
    - iIntros (??[|[[]|][]]) "?"; eauto.
  Qed.

  Lemma tctx_merge_own_prod E L n tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (own_ptr n) tyl 0)
                   [p ◁ own_ptr n $ product tyl].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_own_prod2.
    - iIntros (??[|[[]|][]]) "?"; eauto.
  Qed.

  (** Unique borrows *)
  Lemma tctx_split_uniq_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &uniq{κ}(product2 ty1 ty2)]
                  [p ◁ &uniq{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2].
  Proof.
    iIntros (tid qmax qL) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|]) "[Hp H]"; try done. iDestruct "Hp" as %Hp.
    rewrite /= split_prod_mt. iMod (bor_sep with "LFT H") as "[H1 H2]"; first solve_ndisj.
    rewrite /tctx_elt_interp /=.
    iSplitL "H1"; iExists _; (iSplitR; first by rewrite Hp); auto.
  Qed.

  Lemma tctx_merge_uniq_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &uniq{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2]
                  [p ◁ &uniq{κ}(product2 ty1 ty2)].
  Proof.
    iIntros (tid qmax qL) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]". iDestruct "H1" as ([[]|]) "[Hp1 H1]"; try done.
    iDestruct "Hp1" as %Hp1. iDestruct "H2" as (v2) "(Hp2 & H2)". rewrite /= Hp1.
    iDestruct "Hp2" as %[=<-]. iExists #l. iFrame "%".
    iMod (bor_combine with "LFT H1 H2") as "H"; first solve_ndisj. by rewrite /= split_prod_mt.
  Qed.

  Lemma uniq_is_ptr κ ty tid (vl : list val) :
    ty_own (&uniq{κ}ty) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝.
  Proof. iIntros "H". destruct vl as [|[[]|][]]; eauto. Qed.

  Lemma tctx_split_uniq_prod E L κ tyl p :
    tctx_incl E L [p ◁ &uniq{κ}(product tyl)]
                  (hasty_ptr_offsets p (uniq_bor κ) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_uniq_prod2.
    - intros. apply uniq_is_ptr.
  Qed.

  Lemma tctx_merge_uniq_prod E L κ tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (uniq_bor κ) tyl 0)
                   [p ◁ &uniq{κ}(product tyl)].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_uniq_prod2.
    - intros. apply uniq_is_ptr.
  Qed.

  (** Shared borrows *)
  Lemma tctx_split_shr_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &shr{κ}(product2 ty1 ty2)]
                  [p ◁ &shr{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &shr{κ} ty2].
  Proof.
    iIntros (tid qmax qL) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|]) "[Hp H]"; try iDestruct "H" as "[]".
    iDestruct "H" as "[H1 H2]". iDestruct "Hp" as %Hp.
    by iSplitL "H1"; iExists _; (iSplitR; first by rewrite /= Hp).
  Qed.

  Lemma tctx_merge_shr_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &shr{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &shr{κ} ty2]
                  [p ◁ &shr{κ}(product2 ty1 ty2)].
  Proof.
    iIntros (tid qmax qL) "#LFT _ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]". iDestruct "H1" as ([[]|]) "[Hp1 Hown1]"; try done.
    iDestruct "Hp1" as %Hp1. iDestruct "H2" as ([[]|]) "[Hp2 Hown2]"; try done.
    rewrite /= Hp1. iDestruct "Hp2" as %[=<-]. iExists #l. by iFrame.
  Qed.

  Lemma shr_is_ptr κ ty tid (vl : list val) :
    ty_own (&shr{κ} ty) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝.
  Proof. iIntros "H". destruct vl as [|[[]|][]]; eauto. Qed.

  Lemma tctx_split_shr_prod E L κ tyl p :
    tctx_incl E L [p ◁ &shr{κ}(product tyl)]
                  (hasty_ptr_offsets p (shr_bor κ) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_shr_prod2.
    - intros. apply shr_is_ptr.
  Qed.

  Lemma tctx_merge_shr_prod E L κ tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (shr_bor κ) tyl 0)
                   [p ◁ &shr{κ}(product tyl)].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_shr_prod2.
    - intros. apply shr_is_ptr.
  Qed.

  (* Splitting with [tctx_extract]. *)

  (* We do not state the extraction lemmas directly, because we want the
     automation system to be able to perform e.g., borrowing or splitting after
     splitting. *)
  Lemma tctx_extract_split_own_prod E L p p' n ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (own_ptr n) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ own_ptr n $ Π tyl) :: T) (T' ++ T).
  Proof.
    intros. apply (tctx_incl_frame_r T [_] (_::_)). by rewrite tctx_split_own_prod.
  Qed.

  Lemma tctx_extract_split_uniq_prod E L p p' κ ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (uniq_bor κ) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ &uniq{κ}(Π tyl)) :: T) (T' ++ T).
  Proof.
    intros. apply (tctx_incl_frame_r T [_] (_::_)). by rewrite tctx_split_uniq_prod.
  Qed.

  Lemma tctx_extract_split_shr_prod E L p p' κ ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (shr_bor κ) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ &shr{κ}(Π tyl)) :: T) ((p ◁ &shr{κ}(Π tyl)) :: T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite {1}copy_tctx_incl. apply (tctx_incl_frame_r _ [_] [_]).
    rewrite tctx_split_shr_prod -(contains_tctx_incl _ _ [p' ◁ ty]) //.
    apply submseteq_skip, submseteq_nil_l.
  Qed.

  (* Merging with [tctx_extract]. *)

  Fixpoint extract_tyl E L p (ptr: type → type) tyl (off : nat) T T' : Prop :=
    match tyl with
    | [] => T = T'
    | ty :: tyl => ∃ T'',
        tctx_extract_hasty E L (p +ₗ #off) (ptr ty) T T'' ∧
        extract_tyl E L p ptr tyl (off + ty.(ty_size)) T'' T'
    end.

  Lemma tctx_extract_merge_ptr_prod E L p ptr tyl T T' :
    tctx_incl E L (hasty_ptr_offsets p ptr tyl 0) [p ◁ ptr $ product tyl] →
    extract_tyl E L p ptr tyl 0 T T' →
    tctx_extract_hasty E L p (ptr (Π tyl)) T T'.
  Proof.
    rewrite /extract_tyl /tctx_extract_hasty=>Hi Htyl.
    etrans; last by eapply (tctx_incl_frame_r T' _ [_]). revert T Htyl. clear.
    generalize 0%nat. induction tyl=>[T n /= -> //|T n /= [T'' [-> Htyl]]]. f_equiv. auto.
  Qed.

  Lemma tctx_extract_merge_own_prod E L p n tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (own_ptr n) tyl 0 T T' →
    tctx_extract_hasty E L p (own_ptr n (Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_own_prod. Qed.

  Lemma tctx_extract_merge_uniq_prod E L p κ tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (uniq_bor κ) tyl 0 T T' →
    tctx_extract_hasty E L p (&uniq{κ}(Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_uniq_prod. Qed.

  Lemma tctx_extract_merge_shr_prod E L p κ tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (shr_bor κ) tyl 0 T T' →
    tctx_extract_hasty E L p (&shr{κ}(Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_shr_prod. Qed.
End product_split.

(* We do not want unification to try to unify the definition of these
   types with anything in order to try splitting or merging. *)
Hint Opaque own_ptr uniq_bor shr_bor tctx_extract_hasty : lrust_typing lrust_typing_merge.

(* We make sure that splitting is tried before borrowing, so that not
   the entire product is borrowed when only a part is needed. *)
Hint Resolve tctx_extract_split_own_prod tctx_extract_split_uniq_prod tctx_extract_split_shr_prod
    | 5 : lrust_typing.

(* Merging is also tried after everything, except
   [tctx_extract_hasty_further]. Moreover, it is placed in a
   difference hint db. The reason is that it can make the proof search
   diverge if the type is an evar.

   Unfortunately, priorities are not taken into account accross hint
   databases with [typeclasses eauto], so this is useless, and some
   solve_typing get slow because of that. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5304
*)
Hint Resolve tctx_extract_merge_own_prod tctx_extract_merge_uniq_prod tctx_extract_merge_shr_prod
    | 40 : lrust_typing_merge.
Hint Unfold extract_tyl : lrust_typing.
