From iris.proofmode Require Import tactics.
From lrust.typing Require Import type lft_contexts.
Set Default Proof Using "Type".

Definition path := expr.
Bind Scope expr_scope with path.

(* TODO: Consider making this a pair of a path and the rest. We could
   then e.g. formulate tctx_elt_hasty_path more generally. *)
Inductive tctx_elt `{!typeG Σ} : Type :=
| TCtx_hasty (p : path) (ty : type)
| TCtx_blocked (p : path) (κ : lft) (ty : type).

Notation tctx := (list tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty p ty%list%T) (at level 70).
Notation "p ◁{ κ } ty" := (TCtx_blocked p κ ty)
   (at level 70, format "p  ◁{ κ }  ty").

Section type_context.
  Context `{!typeG Σ}.
  Implicit Types T : tctx.

  Fixpoint eval_path (p : path) : option val :=
    match p with
    | BinOp OffsetOp e (Lit (LitInt n)) =>
      match eval_path e with
      | Some (#(LitLoc l)) => Some (#(l +ₗ n))
      | _ => None
      end
    | e => to_val e
    end.

  Lemma eval_path_of_val (v : val) :
    eval_path v = Some v.
  Proof. destruct v. done. simpl. rewrite (decide_True_pi _). done. Qed.

  Lemma wp_eval_path E p v :
    eval_path p = Some v → ⊢ WP p @ E {{ v', ⌜v' = v⌝ }}.
  Proof.
    revert v; induction p; intros v; try done.
    { intros [=]. by iApply wp_value. }
    { move=> /of_to_val=> ?. by iApply wp_value. }
    simpl. destruct op; try discriminate; [].
    destruct p2; try (intros ?; by iApply wp_value); [].
    destruct l; try (intros ?; by iApply wp_value); [].
    destruct (eval_path p1); try done.
    destruct v0; try discriminate; [].
    destruct l; try discriminate; [].
    intros [=<-]. wp_bind p1. iApply (wp_wand with "[]").
    { iApply IHp1. done. }
    iIntros (v) "%". subst v. wp_op. done.
  Qed.

  Lemma eval_path_closed p v :
    eval_path p = Some v → Closed [] p.
  Proof.
    intros Hpv. revert v Hpv.
    induction p as [| | |[] p IH [|[]| | | | | | | | | |] _| | | | | | | |]=>//.
    - unfold eval_path=>? /of_to_val <-. apply is_closed_of_val.
    - simpl. destruct (eval_path p) as [[[]|]|]; intros ? [= <-].
      specialize (IH _ eq_refl). apply _.
  Qed.

  (** Type context element *)
  Definition tctx_elt_interp (tid : thread_id) (x : tctx_elt) : iProp Σ :=
    match x with
    | p ◁ ty => ∃ v, ⌜eval_path p = Some v⌝ ∗ ty.(ty_own) tid [v]
    | p ◁{κ} ty => ∃ v, ⌜eval_path p = Some v⌝ ∗
                             ([†κ] ={⊤}=∗ ty.(ty_own) tid [v])
    end%I.

  (* Block tctx_elt_interp from reducing with simpl when x is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.

  Lemma tctx_hasty_val tid (v : val) ty :
    tctx_elt_interp tid (v ◁ ty) ⊣⊢ ty.(ty_own) tid [v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (?) "[EQ ?]".
      iDestruct "EQ" as %[=->]. done.
    - iIntros "?". iExists _. auto.
  Qed.

  Lemma tctx_elt_interp_hasty_path p1 p2 ty tid :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) ≡ tctx_elt_interp tid (p2 ◁ ty).
  Proof. intros Hp. rewrite /tctx_elt_interp /=. setoid_rewrite Hp. done. Qed.

  Lemma tctx_hasty_val' tid p (v : val) ty :
    eval_path p = Some v →
    tctx_elt_interp tid (p ◁ ty) ⊣⊢ ty.(ty_own) tid [v].
  Proof.
    intros ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    rewrite eval_path_of_val. done.
  Qed.

  Lemma wp_hasty E tid p ty Φ :
    tctx_elt_interp tid (p ◁ ty) -∗
    (∀ v, ⌜eval_path p = Some v⌝ -∗ ty.(ty_own) tid [v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "Hty HΦ". iDestruct "Hty" as (v) "[% Hown]".
    iApply (wp_wand with "[]"). { iApply wp_eval_path. done. }
    iIntros (v') "%". subst v'. iApply ("HΦ" with "[] Hown"). by auto.
  Qed.

  Lemma closed_hasty tid p ty : tctx_elt_interp tid (p ◁ ty) -∗ ⌜Closed [] p⌝.
  Proof.
    iIntros "H". iDestruct "H" as (?) "[% _]". eauto using eval_path_closed.
  Qed.

  (** Type context *)
  Definition tctx_interp (tid : thread_id) (T : tctx) : iProp Σ :=
    ([∗ list] x ∈ T, tctx_elt_interp tid x)%I.

  Global Instance tctx_interp_permut tid:
    Proper ((≡ₚ) ==> (⊣⊢)) (tctx_interp tid).
  Proof. intros ???. by apply big_opL_permutation. Qed.

  Lemma tctx_interp_cons tid x T :
    tctx_interp tid (x :: T) ⊣⊢ (tctx_elt_interp tid x ∗ tctx_interp tid T).
  Proof. done. Qed.

  Lemma tctx_interp_app tid T1 T2 :
    tctx_interp tid (T1 ++ T2) ⊣⊢ (tctx_interp tid T1 ∗ tctx_interp tid T2).
  Proof. rewrite /tctx_interp big_sepL_app //. Qed.

  Definition tctx_interp_nil tid :
    tctx_interp tid [] = True%I := eq_refl _.

  Lemma tctx_interp_singleton tid x :
    tctx_interp tid [x] ⊣⊢ tctx_elt_interp tid x.
  Proof. rewrite /tctx_interp /= right_id //. Qed.

  (** Copy typing contexts *)
  Class CopyC (T : tctx) :=
    copyc_persistent tid : Persistent (tctx_interp tid T).
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy : CopyC [].
  Proof. rewrite /CopyC. apply _. Qed.

  Global Instance tctx_ty_copy T p ty :
    CopyC T → Copy ty → CopyC ((p ◁ ty) :: T).
  Proof. intros ???. rewrite tctx_interp_cons. apply _. Qed.

  (** Send typing contexts *)
  Class SendC (T : tctx) :=
    sendc_change_tid tid1 tid2 : tctx_interp tid1 T -∗ tctx_interp tid2 T.

  Global Instance tctx_nil_send : SendC [].
  Proof. done. Qed.

  Global Instance tctx_ty_send T p ty :
    SendC T → Send ty → SendC ((p ◁ ty) :: T).
  Proof.
    iIntros (HT Hty ??). rewrite !tctx_interp_cons.
    iIntros "[Hty HT]". iSplitR "HT".
    - iDestruct "Hty" as (?) "[% Hty]". iExists _. iSplit; first done.
      by iApply Hty.
    - by iApply HT.
  Qed.

  (** Type context inclusion *)
  Definition tctx_incl (E : elctx) (L : llctx) (T1 T2 : tctx): Prop :=
    ∀ tid qmax q2, lft_ctx -∗ elctx_interp E -∗ llctx_interp_noend qmax L q2 -∗
              tctx_interp tid T1 ={⊤}=∗ llctx_interp_noend qmax L q2 ∗ tctx_interp tid T2.
  Global Instance : ∀ E L, RewriteRelation (tctx_incl E L) := {}.

  Global Instance tctx_incl_preorder E L : PreOrder (tctx_incl E L).
  Proof.
    split.
    - by iIntros (????) "_ _ $ $".
    - iIntros (??? H1 H2 ???) "#LFT #HE HL H".
      iMod (H1 with "LFT HE HL H") as "(HL & H)".
      by iMod (H2 with "LFT HE HL H") as "($ & $)".
  Qed.

  Lemma contains_tctx_incl E L T1 T2 : T1 ⊆+ T2 → tctx_incl E L T2 T1.
  Proof.
    rewrite /tctx_incl. iIntros (Hc ???) "_ _ $ H". by iApply big_sepL_submseteq.
  Qed.

  Global Instance tctx_incl_app E L :
    Proper (tctx_incl E L ==> tctx_incl E L ==> tctx_incl E L) app.
  Proof.
    intros ?? Hincl1 ?? Hincl2 ???. rewrite /tctx_interp !big_sepL_app.
    iIntros "#LFT #HE HL [H1 H2]".
    iMod (Hincl1 with "LFT HE HL H1") as "(HL & $)".
    iApply (Hincl2 with "LFT HE HL H2").
  Qed.
  Global Instance tctx_incl_cons E L x :
    Proper (tctx_incl E L ==> tctx_incl E L) (cons x).
  Proof. by apply (tctx_incl_app E L [_] [_]). Qed.

  Lemma tctx_incl_frame_l {E L} T T1 T2 :
    tctx_incl E L T1 T2 → tctx_incl E L (T++T1) (T++T2).
  Proof. by apply tctx_incl_app. Qed.
  Lemma tctx_incl_frame_r {E L} T T1 T2 :
    tctx_incl E L T1 T2 → tctx_incl E L (T1++T) (T2++T).
  Proof. by intros; apply tctx_incl_app. Qed.

  Lemma copy_tctx_incl E L p `{!Copy ty} :
    tctx_incl E L [p ◁ ty] [p ◁ ty; p ◁ ty].
  Proof. iIntros (???) "_ _ $ * [#$ $] //". Qed.

  Lemma copy_elem_of_tctx_incl E L T p `{!Copy ty} :
    p ◁ ty ∈ T → tctx_incl E L T ((p ◁ ty) :: T).
  Proof.
    remember (p ◁ ty). induction 1 as [|???? IH]; subst.
    - apply (tctx_incl_frame_r _ [_] [_;_]), copy_tctx_incl, _.
    - etrans. by apply (tctx_incl_frame_l [_]), IH, reflexivity.
      apply contains_tctx_incl, submseteq_swap.
  Qed.

  Lemma type_incl_tctx_incl tid p ty1 ty2 :
    type_incl ty1 ty2 -∗ tctx_interp tid [p ◁ ty1] -∗ tctx_interp tid [p ◁ ty2].
  Proof.
    iIntros "Hincl HT". rewrite !tctx_interp_singleton.
    iDestruct "HT" as (v) "[% HT]". iExists _. iFrame "%".
    iDestruct "Hincl" as "(_ & Hincl & _)". iApply "Hincl". done.
  Qed.
  Lemma subtype_tctx_incl E L p ty1 ty2 :
    subtype E L ty1 ty2 → tctx_incl E L [p ◁ ty1] [p ◁ ty2].
  Proof.
    iIntros (Hst ???) "#LFT #HE HL HT".
    iDestruct (Hst with "HL") as "#Hst". iFrame "HL".
    iApply type_incl_tctx_incl; last done.
    by iApply "Hst".
  Qed.

  (* Extracting from a type context. *)

  Definition tctx_extract_hasty E L p ty T T' : Prop :=
    tctx_incl E L T ((p ◁ ty)::T').
  Lemma tctx_extract_hasty_further E L p ty T T' x :
    tctx_extract_hasty E L p ty T T' →
    tctx_extract_hasty E L p ty (x::T) (x::T').
  Proof. unfold tctx_extract_hasty=>->. apply contains_tctx_incl, submseteq_swap. Qed.
  Lemma tctx_extract_hasty_here_copy E L p1 p2 ty ty' T :
    p1 = p2 → Copy ty → subtype E L ty ty' →
    tctx_extract_hasty E L p1 ty' ((p2 ◁ ty)::T) ((p2 ◁ ty)::T).
  Proof.
    intros -> ??. apply (tctx_incl_frame_r _ [_] [_;_]).
    etrans; first by apply copy_tctx_incl, _.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl.
  Qed.
  Lemma tctx_extract_hasty_here E L p1 p2 ty ty' T :
    p1 = p2 → subtype E L ty ty' → tctx_extract_hasty E L p1 ty' ((p2 ◁ ty)::T) T.
  Proof.
    intros -> ?. by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl.
  Qed.
  Lemma tctx_extract_hasty_here_eq E L p1 p2 ty T :
    p1 = p2 → tctx_extract_hasty E L p1 ty ((p2 ◁ ty)::T) T.
  Proof. intros ->. by apply tctx_extract_hasty_here. Qed.

  Definition tctx_extract_blocked E L p κ ty T T' : Prop :=
    tctx_incl E L T ((p ◁{κ} ty)::T').
  Lemma tctx_extract_blocked_cons E L p κ ty T T' x :
    tctx_extract_blocked E L p κ ty T T' →
    tctx_extract_blocked E L p κ ty (x::T) (x::T').
  Proof.
    move=> /(tctx_incl_frame_l [x]) /= Hincl. rewrite /tctx_extract_blocked.
    etrans; first done. apply contains_tctx_incl, submseteq_swap.
  Qed.
  Lemma tctx_extract_blocked_here E L p κ ty T :
    tctx_extract_blocked E L p κ ty ((p ◁{κ} ty)::T) T.
  Proof. intros. by apply (tctx_incl_frame_r _ [_] [_]). Qed.

  Definition tctx_extract_ctx E L T T1 T2 : Prop :=
    tctx_incl E L T1 (T++T2).
  Lemma tctx_extract_ctx_nil E L T:
    tctx_extract_ctx E L [] T T.
  Proof. by unfold tctx_extract_ctx. Qed.
  Lemma tctx_extract_ctx_hasty E L T T1 T2 T3 p ty:
    tctx_extract_hasty E L p ty T1 T2 → tctx_extract_ctx E L T T2 T3 →
    tctx_extract_ctx E L ((p ◁ ty)::T) T1 T3.
  Proof. unfold tctx_extract_ctx, tctx_extract_hasty=>->->//. Qed.
  Lemma tctx_extract_ctx_blocked E L T T1 T2 T3 p κ ty:
    tctx_extract_blocked E L p κ ty T1 T2 → tctx_extract_ctx E L T T2 T3 →
    tctx_extract_ctx E L ((p ◁{κ} ty)::T) T1 T3.
  Proof. unfold tctx_extract_ctx, tctx_extract_blocked=>->->//. Qed.

  Lemma tctx_extract_ctx_incl E L T T' T0:
    tctx_extract_ctx E L T' T T0 →
    tctx_incl E L T T'.
  Proof.
    unfold tctx_extract_ctx=>->.
      by apply contains_tctx_incl, submseteq_inserts_r.
  Qed.

  (* Unblocking a type context. *)
  (* TODO : That would be great if this could also remove all the
     instances mentionning the lifetime in question.
     E.g., if [p ◁ &uniq{κ} ty] should be removed, because this is now
     useless. *)

  Class UnblockTctx (κ : lft) (T1 T2 : tctx) : Prop :=
    unblock_tctx : ∀ tid, [†κ] -∗ tctx_interp tid T1 ={⊤}=∗ tctx_interp tid T2.

  Global Instance unblock_tctx_nil κ : UnblockTctx κ [] [].
  Proof. by iIntros (tid) "_ $". Qed.

  Global Instance unblock_tctx_cons_unblock T1 T2 p κ ty :
    UnblockTctx κ T1 T2 →
    UnblockTctx κ ((p ◁{κ} ty)::T1) ((p ◁ ty)::T2).
  Proof.
    iIntros (H12 tid) "#H†". rewrite !tctx_interp_cons. iIntros "[H HT1]".
    iMod (H12 with "H† HT1") as "$". iDestruct "H" as (v) "[% H]".
    iExists (v). by iMod ("H" with "H†") as "$".
  Qed.

  Global Instance unblock_tctx_cons κ T1 T2 x :
    UnblockTctx κ T1 T2 → UnblockTctx κ (x::T1) (x::T2) | 100.
  Proof.
    iIntros (H12 tid) "#H†". rewrite !tctx_interp_cons. iIntros "[$ HT1]".
    by iMod (H12 with "H† HT1") as "$".
  Qed.
End type_context.

Global Hint Resolve tctx_extract_hasty_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_hasty_here | 20 : lrust_typing.
Global Hint Resolve tctx_extract_hasty_further | 50 : lrust_typing.
Global Hint Resolve tctx_extract_blocked_here tctx_extract_blocked_cons
             tctx_extract_ctx_nil tctx_extract_ctx_hasty
             tctx_extract_ctx_blocked tctx_extract_ctx_incl : lrust_typing.
Global Hint Opaque tctx_extract_ctx tctx_extract_hasty tctx_extract_blocked
            tctx_incl : lrust_typing.

(* In general, we want reborrowing to be tried before subtyping, so
   that we get the extraction. However, in the case the types match
   exactly, we want to NOT use reborrowing. Therefore, we add
   [tctx_extract_hasty_here_eq] as a hint with a very low cost. *)
Global Hint Resolve tctx_extract_hasty_here_eq | 2 : lrust_typing.
