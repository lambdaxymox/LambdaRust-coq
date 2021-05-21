From iris.proofmode Require Import tactics.
From iris.algebra Require Import csum frac excl agree coPset.
From iris.bi Require Import lib.fractional.
From lrust.lang Require Import proofmode notation.
From lrust.lifetime Require Import meta.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition ghostcellN := lrustN .@ "ghostcell".
Definition ghosttokenN := lrustN .@ "ghosttoken".

(* This library should be valid under weak memory, but the current
   model of Lambdarust-weak makes this challenging to prove. The
   reasons are:

     - The SC model in this file relies crucially on using the atomic accessors
       of borrows, which are much weaker (when they exist) in weakmem. The
       reason of this weakness is that, when we are not in SC, we cannot tel
       that a lifetime is "either alive or dead", since it can be "dead", but
       in a way which is not yet synchronized with the current thread.

   So let's search for another model:
     - We have to prove that successive mutable accesses to the ghost cell are
       synchronized (i.e., they are in happens-before relationship).
     - The only reason these accesses are indeed synchronized is that the *ghost
       token* is transmitted via mechanisms guaranteeing happens-before
       relationship (like every resource transfer in Rust).
     - In particular, when the borrow of a ghost token ends, the ghost token
       needs to change its internal state to remember the view of the death of
       its lifetime. Indeed, the death of the corresponding lifetime is an
       essential link in the synchronization chain between two successive
       accesses to the ghost cell.
     - In the lifetime logic, the only way to allow updates at the death of a
       lifetime is through the "consequence view-shift" of [bor_acc_strong]:
          ▷ Q -∗ [†κ'] ={userE}=∗ ▷ P
     - However, unfortunately, this "consequence view-shift" take a subjective
       version of the death token in weak_mem:
          ▷ Q -∗ subj [†κ'] ={userE}=∗ ▷ P
       As a result, the view at which this view shift is used is independent
       from the actual "view of the death of the lifetime", so we have no
       information about it.
     - The reason why this is a subjective token in weak-mem is because of what
       happens when a non-atomic lifetime dies (a non-atomic lifetime is the
       intersection of other lifetimes). Indeed, a non-atomic lifetime can die
       "several times", once for each component, and each of these death can
       occur at non-comparable views. The only relevant view that we would pass
       to the consequence view-shift is the view used for the inheritance of
       the borrow, but that view is not necessarily well-defined since the
       borrow can be the result of a merging of other borrows.
    Hence, it sounds like that the main blocking point is the merging rule of
    the lifetime logic, which we use very rarely in the model (only for
    merging actual borrows in [tctx_merge_uniq_prod2]). So it might be mossible
    to remove the merging rule from the lifetime logic to get rid of the
    subjective modality in the consequence view-shift and finally get a model
    for GhostCell under weak memory...
  *)

(* States:
   Not borrowed, borrowed.

   Shared states for all borrowed entities:
     Not shared,
     ((lifetime at which shared), borrow fraction).

   "Is borrowed" should agree.
*)

Definition ghosttoken_stR :=
  (csumR (exclR unitO) ((prodR (agreeR lftO) fracR))).

Class ghostcellG Σ := GhostcellG {
  ghostcell_inG :> inG Σ (ghosttoken_stR);
  ghostcell_gsingletonG :> lft_metaG Σ;
}.

Definition ghostcellΣ : gFunctors
  := #[GFunctor ghosttoken_stR ; lft_metaΣ].

Instance subG_ghostcellΣ {Σ} : subG ghostcellΣ Σ → ghostcellG Σ.
Proof. solve_inG. Qed.

(* There are two possible states:
   - None: The GhostToken is currently not used or used in some
     GhostCell::borrow_mut, to get mutable access.
   - Some: The GhostToken is currently used in many GhostCell::get, to get
     shared access. *)
Definition ghosttoken_st := option (lft * frac).

Definition ghosttoken_st_to_R (st : ghosttoken_st) : ghosttoken_stR :=
  (match st with
        | None => Cinl (Excl ())
        | Some p => Cinr ((to_agree p.1, p.2))
        end).

Section ghostcell.
  Context `{!typeG Σ, !ghostcellG Σ}.
  Implicit Types (α β: lft) (γ: gname) (q: Qp) (ty: type) (l: loc).

  Local Instance ghosttoken_fractional γ κ' :
    Fractional (λ q, own γ (ghosttoken_st_to_R (Some (κ',q))))%I.
  Proof.
    rewrite /Fractional=>q1 q2.
    rewrite -own_op /ghosttoken_st_to_R /=. f_equiv.
    rewrite -Cinr_op. f_equiv.
    rewrite -pair_op. f_equiv.
    rewrite agree_idemp. done.
  Qed.

  Program Definition ghosttoken α :=
    tc_opaque
    {| ty_size        := 0;
       ty_own tid vl  :=
         (⌜vl = []⌝ ∗ ∃ γ, lft_meta α γ ∗
          own γ (ghosttoken_st_to_R None))%I;
       ty_shr κ tid l :=
         (∃ γ, lft_meta α γ ∗
           ∃ κ', κ ⊑ κ' ∗
             &frac{κ'}(λ q, own γ (ghosttoken_st_to_R (Some (κ',q)))))%I;
    |}.
  Next Obligation. by iIntros (??[|]) "[% ?]". Qed.
  Next Obligation.
    iIntros (α E κ l tid q ?) "#LFT Hvl Htok".
    iMod (bor_exists with "LFT Hvl") as (vl) "Hvl"; first done.
    iMod (bor_sep with "LFT Hvl") as "[Hvl Hset]"; first done.
    iMod (bor_sep with "LFT Hset") as "[Hp Hset]"; first done.
    iMod (bor_exists with "LFT Hset") as (γ) "Hset"; first done.
    iMod (bor_sep with "LFT Hset") as "[Hidx Hset]"; first done.
    iMod (bor_persistent with "LFT Hidx Htok") as "[>#Hidx Htok]"; first solve_ndisj.
    iMod (bor_acc_strong with "LFT Hset Htok") as (κ') "(#Hκ & >Hset & Hclose)"; first done.
    rewrite bi.sep_exist_r. iExists γ. iFrame "Hidx".
    iMod (own_update _ _ (ghosttoken_st_to_R (Some (κ', 1%Qp))) with "Hset") as "Hset".
    { rewrite /ghosttoken_st_to_R /=. apply cmra_update_exclusive. done. }
    iMod ("Hclose" with "[] Hset") as "[Hset $]".
    { iIntros "!> >Hset _".
      iMod (own_update _ _ (ghosttoken_st_to_R None) with "Hset") as "Hset".
      { rewrite /ghosttoken_st_to_R /=. apply cmra_update_exclusive. done. }
      done. }
    iExists κ'. iMod (bor_fracture with "LFT [Hset]") as "$"; first done.
    { done. }
    eauto.
  Qed.
  Next Obligation.
    iIntros (?????) "#Hκ H".
    iDestruct "H" as (γ) "[#? H]".
    iDestruct "H" as (κ'') "[? ?]".
    iExists _. iFrame "#".
    iExists κ''.
    by iSplit; first iApply lft_incl_trans.
  Qed.
 
  Global Instance ghosttoken_wf α : TyWf (ghosttoken α) :=
    { ty_lfts := [α]; ty_wf_E := [] }.

  Global Instance ghosttoken_ne : NonExpansive ghosttoken := _.

  Global Instance ghosttoken_send α :
    Send (ghosttoken α).
  Proof. done. Qed.

  Global Instance ghosttoken_sync α :
    Sync (ghosttoken α).
  Proof. done. Qed.

  Global Instance ghosttoken_mono E L :
    Proper (lctx_lft_eq E L ==> subtype E L) ghosttoken.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (α1 α2 [EQ1 EQ2] qmax qL) "HL".
    iDestruct (EQ1 with "HL") as "#EQ1'".
    iDestruct (EQ2 with "HL") as "#EQ2'".
    iIntros "!> #HE".
    iDestruct ("EQ1'" with "HE") as %EQ1'.
    iDestruct ("EQ2'" with "HE") as %EQ2'.
    iSplit; [|iSplit; iIntros "!> * H"]; simpl.
    - iPureIntro; congruence.
    - solve_proper_prepare.
      iDestruct "H" as "[$ H]".
      iDestruct "H" as (γ) "H".
      iExists γ; iDestruct "H" as "[H $]".
      by rewrite (lft_incl_syn_anti_symm _ _ EQ1' EQ2').
    - iDestruct "H" as (γ) "H".
      iExists γ; iDestruct "H" as "[H  $]".
      by rewrite (lft_incl_syn_anti_symm _ _ EQ1' EQ2').
  Qed.

  Global Instance ghosttoken_mono'
    E L : Proper (lctx_lft_eq E L ==> eqtype E L) ghosttoken.
  Proof.
    intros.
    split; by apply ghosttoken_mono.
  Qed.

  (** β is the total sharing lifetime of the GhostCell.
      (In the proofs below, β is often something else!) *)
  Definition ghostcell_inv tid l β α ty : iProp Σ :=
    (∃ st',
      match st' with
      | None => &{β}(l ↦∗: ty.(ty_own) tid) (* ghostcell is not currently being accessed *)
      | Some rw => ∃ γ, lft_meta α γ ∗
          match rw with
          | true => (* ghostcell is currently being write-accessed *)
              (* The κ' will be set to the lifetime β in borrow_mut, the lifetime
              for which we exclusively have the borrow token.  If we own the
              ghost token fragment (in any state), then at any time either κ'
              still runs (so we get a contradiction when opening the borrow
              here) or we can run the inheritance to get back the full
              borrow. *)
              ∃ κ', &{κ'} (own γ (ghosttoken_st_to_R None)) ∗
                    ([†κ'] ={↑lftN}=∗ &{β} (l ↦∗: ty_own ty tid))
          | false => (* ghostcell is currently being read-accessed *)
              (* The κ' will be set to the total lifetime for which the token is
              shared.  If we own the ghost token fragment in [None] state, then
              we can deduce κ' is dead and we get back the full borrow. If we
              own it in [Some] state we know the κ' is equal to the one in our
              token, which outlives the lifetime of the token borrow that we got
              (that is ensures in the GhostToken sharing interpretation), which
              means it lives long enough to return it to the caller at that
              lifetime. *)
              ∃ κ', &frac{κ'} (λ q', own γ (ghosttoken_st_to_R (Some (κ', q')))) ∗
                    ([†κ'] ={↑lftN}=∗ &{β}(l ↦∗: ty.(ty_own) tid)) ∗
                    ty.(ty_shr) (β ⊓ κ') tid l
          end
      end)%I.

  Global Instance ghostcell_inv_type_ne n tid l β α :
    Proper (type_dist2 n ==> dist n) (ghostcell_inv tid l β α).
  Proof.
    solve_proper_core
      ltac:(fun _ => exact: type_dist2_S || f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance ghostcell_inv_ne tid l β α : NonExpansive (ghostcell_inv tid l β α).
  Proof.
    intros n ???. by eapply ghostcell_inv_type_ne, type_dist_dist2.
  Qed.

  Lemma ghostcell_inv_proper E L κ1 κ2 ty1 ty2 qmax qL :
    lctx_lft_eq E L κ1 κ2 →
    eqtype E L ty1 ty2 →
    llctx_interp_noend qmax L qL -∗ ∀ tid l β, □ (elctx_interp E -∗
    ghostcell_inv tid l β κ1 ty1 -∗ ghostcell_inv tid l β κ2 ty2).
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic. *)
    (*             It would easily gain from some automation. *)
    rewrite eqtype_unfold. iIntros ([Hlft1 Hlft2] Hty) "HL".
    iDestruct (Hty with "HL") as "#Hty".
    iDestruct (Hlft1 with "HL") as "#Hlft1".
    iDestruct (Hlft2 with "HL") as "#Hlft2".
    iIntros (tid l β) "!> #HE H".
    iDestruct ("Hty" with "HE") as "(% & #Hown & #Hshr)".
    iDestruct ("Hlft1" with "HE") as %Hκ1.
    iDestruct ("Hlft2" with "HE") as %Hκ2.
    iAssert (□ (&{β}(l ↦∗: ty_own ty1 tid) -∗
                &{β}(l ↦∗: ty_own ty2 tid)))%I as "#Hb".
    { iIntros "!> H". iApply bor_iff; last done.
      iNext; iModIntro; iSplit; iIntros "H"; iDestruct "H" as (vl) "[Hf H]"; iExists vl;
      iFrame; by iApply "Hown". }
    iDestruct "H" as (rw) "H"; iExists rw; destruct rw as [rw|]; iFrame "∗";
      last by iApply "Hb"; last first.
    iDestruct "H" as (γc) "(#Hsing&H)".
    iExists γc.
    iSplitR.
    { by rewrite (lft_incl_syn_anti_symm _ _ Hκ1 Hκ2). }
    destruct rw.
    { iDestruct "H" as (κ') "H'".
      iExists κ'; iDestruct "H'" as "($ & H')".
      iIntros "Hκ'". iMod ("H'" with "Hκ'"). by iApply "Hb". }
    iDestruct "H" as (κ') "(Hag&Hh&H)"; iExists κ'; iFrame "Hag".
    iSplitL "Hh"; last by iApply "Hshr".
    iIntros "Hν". iMod ("Hh" with "Hν") as "Hh".
    by iApply "Hb".
  Qed.

  (* Idea:
     Ghostcell is basically a refcell/rwlock.  Main difference being that current r/w state is
     not directly tied to any physical state (for ty_shr); in other words, you can't really do
     anything with just a ghostcell.  The ghosttoken is responsible for tracking the r/w state of any
     ghostcells that are currently open.  A share of a ghosttoken always tracks the exact fraction
     that it is sharing.  It may not actually be necessary for the ghosttoken to track these things
     explicitly, since a read borrow is the same as a regular borrow.

     Key point: you don't really need to prove you can go from a borrow back to the original
     resource under normal circumstances.  For atomic borrows you just need to show that the
     thing inside the atomic borrow holds initially (which can just be the original borrow you
     got plus some ownership of ghost state, if you want).  To *update* an atomic borrow, you
     just have to show you can go back to the original resource *or* the token is dead.
     To update an original borrow (and not change the mask) you need to show that the token is
     alive initially, and that the resource to which you want to update it can move back to P
     with the empty mask and no access to the token you povided.  bor_acc_atomic and friends do
     other stuff.

    (when the lifetime is dead it can
     be removed from the track set).
  *)
  Program Definition ghostcell (α : lft) (ty : type) :=
    tc_opaque
    {| ty_size        := ty.(ty_size);
       ty_own tid vl  := ty.(ty_own) tid vl;
       ty_shr κ tid l :=
         (∃ β, κ ⊑ β ∗ &at{β, ghostcellN}(ghostcell_inv tid l β α ty))%I |}.
  Next Obligation.
    iIntros (????) "H". by rewrite ty_size_eq.
  Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q ?) "#LFT Hvl [Htok Htok']".
    iAssert ((q / 2).[κ] ∗ ▷ ghostcell_inv tid l κ α ty)%I with "[> -Htok]"
      as "[$ HQ]"; last first.
    { iFrame "Htok".
      iExists κ.
      iSplitR; first by iApply lft_incl_refl.
      iMod (bor_create _ κ with "LFT HQ") as "[HQ HQ']"; first done.
      iApply bor_share; first solve_ndisj.
      iFrame "∗". }
    iFrame. iExists None. by iFrame.
  Qed.
  Next Obligation.
    iIntros (??????) "#Hκ H". iDestruct "H" as (β) "H".
    iExists β; iDestruct "H" as "[? $]".
    by iApply lft_incl_trans.
  Qed.

  Global Instance ghostcell_wf α `{!TyWf ty} : TyWf (ghostcell α ty) :=
    { ty_lfts := α::ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

  Global Instance ghostcell_type_ne α : TypeNonExpansive (ghostcell α).
  Proof.
    constructor;
      solve_proper_core ltac:(
        fun _ => exact: type_dist2_S || (eapply ghostcell_inv_type_ne; try reflexivity) ||
                        (eapply ghostcell_inv_proj_type_ne; try reflexivity) ||
                                              f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance ghostcell_ne α : NonExpansive (ghostcell α).
  Proof.
    constructor; solve_proper_core ltac:(
                   fun _ => (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance ghostcell_mono E L : Proper (lctx_lft_eq E L ==> eqtype E L ==> subtype E L)
                                               (ghostcell).
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (κ κ' [EQ1 EQ1'] ty1 ty2 EQ2 qmax qL) "HL". generalize EQ2. rewrite eqtype_unfold=>EQ'2.
    iDestruct (EQ1 with "HL") as "#EQ1".
    iDestruct (EQ1' with "HL") as "#EQ1'".
    iDestruct (EQ'2 with "HL") as "#EQ'".
    iDestruct (ghostcell_inv_proper _ _ κ κ' with "HL") as "#Hty1ty2"; [done|done|].
    iDestruct (ghostcell_inv_proper _ _ κ' κ with "HL") as "#Hty2ty1"; [done|by symmetry|].
    iIntros "!> #HE". iDestruct ("EQ'" with "HE") as "(% & #Hown & #Hshr)".
    iSplit; [|iSplit; iIntros "!> * H"]; simpl.
    - iPureIntro; congruence.
    - by iApply "Hown".
    - iDestruct "H" as (a) "H".
      iExists a; iDestruct "H" as "[$ H]".
      iApply at_bor_iff; last done.
      iNext; iModIntro; iSplit; iIntros "H"; by [iApply "Hty1ty2"|iApply "Hty2ty1"].
  Qed.

  Lemma ghostcell_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_eq E L κ1 κ2 →
    eqtype E L ty1 ty2 →
    subtype E L (ghostcell κ1 ty1) (ghostcell κ2 ty2).
  Proof. intros. by eapply ghostcell_mono. Qed.

  Global Instance ghostcell_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) ghostcell.
  Proof. by split; apply ghostcell_mono. Qed.

  Lemma ghostcell_proper' E L κ1 κ2 ty1 ty2 :
    lctx_lft_eq E L κ1 κ2 →
    eqtype E L ty1 ty2 →
    eqtype E L (ghostcell κ1 ty1) (ghostcell κ2 ty2).
  Proof. intros. by apply ghostcell_proper. Qed.

  Hint Resolve ghostcell_mono' ghostcell_proper' : lrust_typing.

  Global Instance ghostcell_send α ty :
    Send ty → Send (ghostcell α ty).
  Proof. by unfold ghostcell, Send. Qed.

  Global Instance ghostcell_sync α ty :
    Send ty → Sync ty → Sync (ghostcell α ty).
  Proof.
    intros Hsend Hsync ????.
    solve_proper_prepare.
    do 3 f_equiv.
    unfold ghostcell_inv.
    rewrite at_bor_proper; first done.
    do 7 f_equiv.
    - do 9 f_equiv. iApply send_change_tid'.
    - do 4 f_equiv; last by iApply sync_change_tid'.
      do 6 f_equiv. iApply send_change_tid'.
    - iApply send_change_tid'.
  Qed.

  Definition ghosttoken_new (call_once : val) (R_F : type) : val :=
    fn: ["f"] :=
      let: "call_once" := call_once in
      let: "n" := new [ #0] in
      letcall: "r" := "call_once" ["f";"n"]%E in
      letalloc: "r'" <-{ R_F.(ty_size)} !"r" in
      delete [ #R_F.(ty_size); "r"];;
      return: ["r'"].

  Lemma ghosttoken_new_type F R_F call_once `{!TyWf F, !TyWf R_F} :
    typed_val call_once (fn(∀ α, ∅; F, ghosttoken α) → R_F) →
    typed_val (ghosttoken_new call_once R_F) (fn(∅; F) → R_F).
  Proof.
    iIntros (Hf E L). iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret args). inv_vec args=>env. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (f); simpl_subst.
    iApply type_new_subtype; [solve_typing..|].
    iIntros (n).
    simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hc (Hn & Hf & Henv & _)".
    iMod (lctx_lft_alive_tok (ϝ) with "HE HL")
      as (qϝf) "(Hϝf & HL & Hclosef)"; [solve_typing..|].
    iMod (own_alloc (ghosttoken_st_to_R None)) as (γ) "Hown"; first done.
    iMod (lft_create_meta γ with "LFT") as (α) "[#Hidx [Htok #Hα]]"; first done.
    wp_let.
    rewrite !tctx_hasty_val.
    iDestruct (lft_intersect_acc with "Htok Hϝf") as (?) "[Hαϝ Hcloseα]".
    iApply (type_call_iris _ [α; ϝ] (α) [_;_] _ _ _ _
              with "LFT HE Hna [Hαϝ] Hf [Hn Henv Hown]"); try solve_typing.
    + by rewrite /= (right_id static).
    + rewrite /= (right_id emp%I) !tctx_hasty_val ownptr_uninit_own.
      iFrame "Henv".
      rewrite ownptr_own.
      iDestruct "Hn" as (l vl) "(% & Hl & Hfree)".
      iExists l, vl.
      iSplit; first done.
      simpl_subst.
      iFrame.
      iSplit; first by refine (match vl with Vector.nil => _ end).
      iExists γ.
      by iFrame "Hidx Hown".
    + iIntros (r) "Hna Hf Hown".
      simpl_subst.
      iDestruct ("Hcloseα" with "[Hf]") as "[Htok Hf]"; [by rewrite (right_id static)|].
      iMod ("Hclosef" with "Hf HL") as "HL".
      wp_let.
      iApply (type_type _ _ _ [ r ◁ box R_F ] with "[] LFT HE Hna HL Hc"); try solve_typing;
        last by rewrite !tctx_interp_singleton tctx_hasty_val.
      iApply type_letalloc_n; [solve_typing..|].
      iIntros (r').
      simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition ghostcell_new : val :=
    fn: ["n"] :=
      return: ["n"].

  Lemma ghostcell_new_type `{!TyWf ty} :
    typed_val ghostcell_new (fn(∀ α, ∅; ty) → (ghostcell α ty))%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (α ϝ ret args). inv_vec args=>n. simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hk Hn".
    rewrite tctx_interp_singleton tctx_hasty_val.
    iAssert (ty_own (box (ghostcell α ty)) tid [n])%I with "[Hn]" as "Hn".
    { rewrite !ownptr_own.
      iDestruct "Hn" as (l vl) "(% & Hl & Hown & Hfree)".
      by iExists l, vl; simpl; iFrame "Hl Hown Hfree". }
    rewrite -tctx_hasty_val -tctx_interp_singleton.
    iApply (type_type with "[] LFT HE Hna HL Hk Hn").
    iApply type_jump; solve_typing.
  Qed.

  Definition ghostcell_borrow : val :=
    fn: ["c";"s"] :=
      (* Skips needed for laters *)
      Skip ;; Skip ;;
      return: ["c"].

  Lemma ghostcell_share E qβ β κ' tid lc γ κ α ty :
    ↑lftN ⊆ E →
    ⊢ (lft_ctx -∗
    β ⊑ κ -∗
    β ⊑ κ' -∗
    &frac{κ'} (λ q : Qp, own γ (ghosttoken_st_to_R (Some (κ', q)))) -∗
    (qβ).[β] -∗
    lft_meta α γ -∗
    &{κ} (lc ↦∗: ty_own ty tid) ={E}=∗
      ▷ ghostcell_inv tid lc κ α ty ∗
      ty_shr ty β tid lc ∗ (qβ).[β]).
  Proof.
    iIntros (HE) "#LFT #Hκ #Hβκ' #Hfractok [Hβ1 Hβ2] Hsing Hst'".
    iMod (fupd_mask_subseteq (↑lftN)) as "Hclose"; first solve_ndisj.
    iMod (lft_incl_acc with "Hκ Hβ1") as (q''2) "[Hq'' Hcloseq'']"; first solve_ndisj.
    iMod (lft_incl_acc with "Hβκ' Hβ2") as (q''2_2) "[Hq''_2 Hcloseq''_2]";
      first solve_ndisj.
    iMod (rebor _ _ (κ ⊓ κ') (lc ↦∗: ty_own ty tid)%I with "LFT [] [Hst']")
      as "[Hvl Hh]"; [done|iApply lft_intersect_incl_l|done|].
    iDestruct (lft_intersect_acc with "Hq'' Hq''_2") as (q''3) "[Hq'' Hcloseq''2]".
    iMod (ty_share with "LFT Hvl Hq''") as "[#Hshr Hq'']"; first solve_ndisj.
    iDestruct ("Hcloseq''2" with "Hq''") as "[Hq'' Hq''_2]".
    iMod ("Hcloseq''" with "Hq''") as "$".
    iMod ("Hcloseq''_2" with "Hq''_2") as "$".
    iDestruct (ty_shr_mono with "[] Hshr") as "$"; first by iApply lft_incl_glb.
    iMod "Hclose" as "_".
    iExists (Some false), γ; iFrame "Hsing".
    iExists κ'; iFrame "#∗". iIntros "!> !> Htok".
    iApply "Hh". iApply lft_dead_or. by iRight.
  Qed.

  Lemma ghostcell_borrow_type `{!TyWf ty} :
    typed_val ghostcell_borrow
              (fn(∀ '(α, β), ∅; &shr{β} (ghostcell α ty), &shr{β} (ghosttoken α)) →
                  &shr{β} ty)%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros ([α β] ϝ ret args). inv_vec args=>c s. simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL HC (Hc & Hs & _)".
    rewrite !tctx_hasty_val.
    iMod (lctx_lft_alive_tok β with "HE HL")
      as (qβ) "([Hβ1 [Hβ2 Hβ3]] & HL & Hclose)"; [solve_typing..|].
    iAssert (▷ |={⊤}[⊤∖↑ghostcellN]▷=> (ty_own (box (&shr{β} ty)) tid [c] ∗ (qβ).[β]))%I
      with "[Hβ1 Hβ2 Hβ3 Hs Hc]"as "Hc".
    { iClear "HE".
      rewrite (ownptr_own (_ (_ (ghostcell _ _))))
              (ownptr_own (_ (&shr{β} ty)))%T.
      rewrite ownptr_own.
      iDestruct "Hs" as (l' vl') "(_ & _ & Hats & _)".
      iDestruct "Hc" as (l vl) "(% & Hl & Hatc & Hfree)".
      subst.
      inv_vec vl'=>ls'.
      iAssert _ with "Hats" as "#Hats'".
      iDestruct (shr_is_ptr with "Hats'") as (ls) "> H". iDestruct "H" as %H.
      inversion H; subst; iClear (H) "Hats'".
      inv_vec vl=>lc'.
      iAssert _ with "Hatc" as "#Hatc'".
      iDestruct (shr_is_ptr with "Hatc'") as (lc)  "> H". iDestruct "H" as %H.
      inversion H; simpl_subst; iClear (H) "Hatc'".
      iDestruct "Hats" as (γ) "[Hsing Hats]".
      iDestruct "Hats" as (κ') "[#Hβκ' #Hats]".
      iDestruct "Hatc" as (κ) "[#Hκ Hatc]".
      iDestruct (at_bor_shorten with "Hκ Hatc") as "Hatc'".
      iIntros "!>".
      iMod (at_bor_acc_tok with "LFT Hatc' Hβ1") as "[Hcell Hclosec]"; [solve_ndisj..|].
      iDestruct "Hcell" as (st') "Hst'".
      destruct st' as [rw|].
      { iDestruct "Hst'" as (γ') "(>Hsing' & Hst')".
        iDestruct (lft_meta_agree with "Hsing Hsing'") as %<-.
        iClear "Hsing'".
        iIntros "!> !>".
        iMod (fupd_mask_subseteq (↑lftN)) as "Hclose"; first solve_ndisj.
        iDestruct (frac_bor_shorten with "Hβκ' Hats") as "Hats'".
        iMod (frac_bor_acc with "LFT Hats' Hβ2") as (q') "[>Hset Hcloses] {Hats'}"; [solve_ndisj..|].
        destruct rw as[|].
        { iDestruct "Hst'" as (κ'0) "(Hbor & Hdead)".
          iMod (bor_acc_atomic with "LFT Hbor") as "[[> Hst' Hcloseb]|[H† Hcloseb]]"; first done.
          - iDestruct (own_valid_2 with "Hset Hst'") as %[].
          - iMod "Hcloseb" as "_".
            iMod ("Hdead" with "H†") as "Hst'".
            iMod ("Hcloses" with "Hset") as "Hβ2".
            iMod "Hclose" as "_".
            iMod (ghostcell_share with "LFT Hκ Hβκ' Hats Hβ3 Hsing Hst'")
              as "(Hinv' & Hshr & Hβ3)"; first solve_ndisj.
            iMod ("Hclosec" with "Hinv'") as "$".
            iFrame "Hβ3 Hβ2".
            iModIntro.
            iExists l, (Vector.cons #lc Vector.nil).
            by iFrame "Hshr Hl Hfree". }
        iDestruct "Hst'" as (κ'0) "(Hκ'0bor & Hνκ & #Hshrκ)".
        iMod (frac_bor_atomic_acc with "LFT Hκ'0bor")
          as "[Hsucc|[Hκ'0† >_]]"; first done; last first.
        { iMod ("Hνκ" with "Hκ'0†") as "Hst'".
          iClear "Hshrκ".
          iMod ("Hcloses" with "Hset") as "Hβ2".
          iMod "Hclose" as "_".
          iMod (ghostcell_share with "LFT Hκ Hβκ' Hats Hβ3 Hsing Hst'")
            as "(Hinv' & Hshr & Hβ3)"; first solve_ndisj.
          iMod ("Hclosec" with "Hinv'") as "$".
          iFrame "Hβ3 Hβ2".
          iModIntro.
          iExists l, (Vector.cons #lc Vector.nil).
          by iFrame "Hshr Hl Hfree". }
        iDestruct "Hsucc" as (q'0) "[>Hownκ'0 Hcloseκ'0]".
        iDestruct (own_valid_2 with "Hset Hownκ'0") as %Hvalidκ'0.
        (* Argue that we have the same κ' here as the already existing sharing protocol. *)
        assert (Hκ'κ'0 : κ' = κ'0).
        { move: Hvalidκ'0. rewrite /ghosttoken_st_to_R /=.
          rewrite -Cinr_op /valid /cmra_valid /=.
          rewrite pair_valid /=.
          intros [?%to_agree_op_inv_L _]. done. }
        subst κ'0.
        iMod ("Hcloseκ'0" with "Hownκ'0") as "_".
        iDestruct (ty_shr_mono with "[] Hshrκ") as "Hshrβ"; first by iApply lft_incl_glb.
        iMod ("Hcloses" with "Hset") as "Hβ2".
        iMod "Hclose" as "_".
        iMod ("Hclosec" with "[Hνκ Hsing]") as "$".
        { iNext.
          iExists (Some false).
          iExists γ.
          iFrame "Hsing".
          iExists κ'.
          by iFrame "Hνκ Hshrκ". }
        iFrame "Hβ3 Hβ2".
        iExists l, (Vector.cons #lc Vector.nil).
        by iFrame "Hshrβ Hl Hfree". }
      iIntros "!> !>".
      iMod (fupd_mask_subseteq (↑lftN)) as "Hclose"; first solve_ndisj.
      iMod "Hclose" as "_".
      iMod (ghostcell_share with "LFT Hκ Hβκ' Hats Hβ3 Hsing Hst'")
        as "(Hinv' & Hshr & Hβ3)"; first solve_ndisj.
      iMod ("Hclosec" with "Hinv'") as "$".
      iFrame "Hβ3 Hβ2".
      iModIntro.
      iExists l, (Vector.cons #lc Vector.nil).
      by iFrame "Hshr Hl Hfree". }
    wp_let.
    iApply lifting.wp_pure_step_fupd; first done.
    iMod "Hc".
    iIntros "!> !>".
    iMod "Hc".
    iDestruct "Hc" as "[Hshr Hβ]".
    iMod ("Hclose" with "Hβ HL") as "HL".
    iIntros "!>".
    do 2 wp_let.
    iApply (type_type _ _ _ [c ◁  box (&shr{β} ty)]
              with "[] LFT HE Hna HL HC [Hshr]"); last first.
    { by rewrite tctx_interp_singleton tctx_hasty_val. }
    iApply type_jump; solve_typing.
  Qed.

  Definition ghostcell_borrow_mut : val :=
    fn: ["c";"s"] :=
      (* Skips needed for laters *)
      Skip ;; Skip ;;
      return: ["c"].

  Lemma ghostcell_borrow_mut_type `{!TyWf ty} :
    typed_val ghostcell_borrow_mut
              (fn(∀ '(α, β), ∅; &shr{β} (ghostcell α ty), &uniq{β} (ghosttoken α)) →
                  &uniq{β} ty)%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros ([α β] ϝ ret args). inv_vec args=>c s. simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL HC (Hc & Hs & _)".
    rewrite !tctx_hasty_val.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "([Hβ1 [Hβ2 Hβ3]] & HL & Hclose)";
      [solve_typing..|].
    iAssert (▷ |={⊤}[⊤∖↑ghostcellN]▷=> (ty_own (box (&uniq{β} ty)) tid [c] ∗ (qβ).[β]))%I
      with "[Hβ1 Hβ2 Hβ3 Hs Hc]"as "Hc".
    { iClear "HE".
      rewrite (ownptr_own (_ (_ (ghostcell _ _))))
              (ownptr_own (_ (&uniq{β} ty)))%T.
      rewrite ownptr_own.
      iDestruct "Hs" as (l' vl') "(_ & _ & Hats & _)".
      iDestruct "Hc" as (l vl) "(% & Hl & Hatc & Hfree)".
      subst.
      inv_vec vl'=>ls'.
      destruct ls' as [[|ls|]|]; try by iDestruct "Hats" as "> []".
      inv_vec vl=>lc'.
      iAssert _ with "Hatc" as "#Hatc'".
      iDestruct (shr_is_ptr with "Hatc'") as (lc) "> H". iDestruct "H" as %H.
      inversion H; simpl_subst; iClear (H) "Hatc'".
      iDestruct "Hatc" as (κ) "[#Hκ Hatc]".
      iDestruct (at_bor_shorten with "Hκ Hatc") as "Hatc'".
      iIntros "!>".
      iMod (at_bor_acc_tok with "LFT Hatc' Hβ1") as "[Hcell Hclosec]"; [solve_ndisj..|].
      iDestruct "Hcell" as (st') "Hst'".
      iMod (bor_acc_strong with "LFT Hats Hβ2") as (κ'1) "[#Hκ'κ'1 [Hats Hcloses]]"; first solve_ndisj.
      iDestruct "Hats" as (vl) "(> Hls & > % & >Hats)".
      subst vl.
      iDestruct "Hats" as (γ) "[#Hsing Hset]".
      iAssert ((|={⊤ ∖ ↑ghostcellN}▷=>
                own γ (Cinl (Excl ())) ∗
                 (&{κ} (lc ↦∗: ty_own ty tid))) (* ∨
               (_ ∗ ▷ ghostcell_inv tid lc κ α ty ∗ |={⊤}▷=> ▷ ▷ False) *) )%I
        with "[Hst' Hset]" as "Hown".
      { destruct st' as [rw|]; last first.
        { eauto with iFrame. }
        iDestruct "Hst'" as (γ') "(>Hsing' & Hst')".
        iDestruct (lft_meta_agree with "Hsing Hsing'") as %<-.
        iClear "Hsing'".
        iIntros "!> !>".
        iMod (fupd_mask_subseteq (↑lftN)) as "Hclose"; first solve_ndisj.
        destruct rw as [|].
        { iDestruct "Hst'" as (κ'0) "(Hbor & Hdead)".
          iMod (bor_acc_atomic with "LFT Hbor") as "[[> Hst' Hcloseb]|[H† Hcloseb]]";
            first done.
          { iDestruct (own_valid_2 with "Hset Hst'") as %[]. }
          iMod "Hcloseb" as "_".
          iMod ("Hdead" with "H†") as "Hst'".
          iFrame. done. }
        iDestruct "Hst'" as (κ') "(Hst' & Hνκ & #Hshrκ)".
        iDestruct "Hst'" as "Hκ'0bor".
        iClear "Hshrκ".
        iMod (frac_bor_atomic_acc with "LFT Hκ'0bor") as "[Hsucc|[H Hcloseb]]"; first done.
        { iDestruct "Hsucc" as (q) "[>Htok _]".
          iDestruct (own_valid_2 with "Hset Htok") as %[]. }
        iMod "Hcloseb" as "_".
        iMod ("Hνκ" with "H") as "$".
        iMod "Hclose".
        by iFrame. }
      iMod "Hown".
      iIntros "!> !>".
      iMod "Hown" as "[Hset Hown]".
      iMod ("Hcloses" $! (own γ (ghosttoken_st_to_R None)) with "[Hls] Hset") as "[Hset Hβ]".
      { iIntros "!> >Hset _". iExists []. eauto 10 with iFrame. }
      iMod (fupd_mask_subseteq (↑lftN)) as "Hclose"; first solve_ndisj.
      iMod (rebor with "LFT Hκ Hown") as "[Hbor Hcloseβ]"; first solve_ndisj.
      iMod "Hclose" as "_".
      iMod ("Hclosec" with "[Hcloseβ Hset]") as "$".
      { iExists (Some true), γ.
        iFrame "Hsing". iExists β; iFrame. iNext.
        iApply bor_shorten; last done. done.
      }
      iFrame "Hβ3 Hβ".
      iExists l, (Vector.cons #lc Vector.nil).
      iAssert (⌜#l = #l⌝)%I as "$"; first done.
      by iFrame "Hl Hfree Hbor". }
    wp_let.
    iApply lifting.wp_pure_step_fupd; first done.
    iMod "Hc".
    iIntros "!> !>".
    iMod "Hc".
    iDestruct "Hc" as "[Hshr Hβ]".
    iMod ("Hclose" with "Hβ HL") as "HL".
    iIntros "!>".
    do 2 wp_let.
    iApply (type_type _ _ _ [c ◁  box (&uniq{β} ty)]
              with "[] LFT HE Hna HL HC [Hshr]"); last first.
    { by rewrite tctx_interp_singleton tctx_hasty_val. }
    iApply type_jump; solve_typing.
  Qed.

  Definition ghostcell_as_mut : val :=
    fn: ["c"] :=
      return: ["c"].

  Lemma ghostcell_as_mut_type `{!TyWf ty} :
    typed_val ghostcell_as_mut (fn(∀ '(α, β), ∅; &uniq{β} (ghostcell α ty)) →
                                  &uniq{β} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros ([α β] ϝ ret args). inv_vec args=>c. simpl_subst.
    iIntros (tid qmax) "#LFT #HE Hna HL Hk Hc".
    rewrite tctx_interp_singleton tctx_hasty_val.
    iAssert (ty_own (box (&uniq{β} ty)) tid [c])%I with "[Hc]" as "Hc".
    { rewrite !ownptr_own.
      iDestruct "Hc" as (l vl) "(% & Hl & Hown & Hfree)".
      iExists l, vl; rewrite /ty_own /=. by iFrame "Hl Hown Hfree". }
    rewrite -tctx_hasty_val -tctx_interp_singleton.
    iApply (type_type with "[] LFT HE Hna HL Hk Hc").
    iApply type_jump; solve_typing.
  Qed.

End ghostcell.
