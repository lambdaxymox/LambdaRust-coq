From iris.proofmode Require Import tactics.
From lrust.lang Require Import notation.
From lrust.typing Require Import type lft_contexts type_context.
Set Default Proof Using "Type".

Section cont_context_def.
  Context `{!typeG Σ}.

  Definition cont_postcondition : iProp Σ := True%I.

  Record cctx_elt : Type :=
    CCtx_iscont { cctxe_k : val; cctxe_L : llctx;
                  cctxe_n : nat; cctxe_T : vec val cctxe_n → tctx }.
End cont_context_def.
Add Printing Constructor cctx_elt.

Notation cctx := (list cctx_elt).

Notation "k ◁cont( L , T )" := (CCtx_iscont k L _ T)
  (at level 70, format "k  ◁cont( L ,  T )").

Section cont_context.
  Context `{!typeG Σ}.

  Definition cctx_elt_interp (tid : thread_id) (qmax: Qp) (x : cctx_elt) : iProp Σ :=
    let '(k ◁cont(L, T)) := x in
    (∀ args, na_own tid top -∗ llctx_interp qmax L -∗ tctx_interp tid (T args) -∗
         WP k (of_val <$> (args : list _)) {{ _, cont_postcondition }})%I.
  Definition cctx_interp (tid : thread_id) (qmax: Qp) (C : cctx) : iProp Σ :=
    (∀ (x : cctx_elt), ⌜x ∈ C⌝ -∗ cctx_elt_interp tid qmax x)%I.

  Global Instance cctx_interp_permut tid qmax :
    Proper ((≡ₚ) ==> (⊣⊢)) (cctx_interp tid qmax).
  Proof. solve_proper. Qed.

  Lemma cctx_interp_cons tid qmax x T :
    cctx_interp tid qmax (x :: T) ≡ (cctx_elt_interp tid qmax x ∧ cctx_interp tid qmax T)%I.
  Proof.
    iSplit.
    - iIntros "H". iSplit; [|iIntros (??)]; iApply "H"; rewrite elem_of_cons; auto.
    - iIntros "H". iIntros (? Hin). revert Hin. rewrite elem_of_cons=>-[->|?].
      + by iDestruct "H" as "[H _]".
      + iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

  Lemma cctx_interp_nil tid qmax : cctx_interp tid qmax [] ≡ True%I.
  Proof. iSplit; first by auto. iIntros "_". iIntros (? Hin). inversion Hin. Qed.

  Lemma cctx_interp_app tid qmax T1 T2 :
    cctx_interp tid qmax (T1 ++ T2) ≡ (cctx_interp tid qmax T1 ∧ cctx_interp tid qmax T2)%I.
  Proof.
    induction T1 as [|?? IH]; first by rewrite /= cctx_interp_nil left_id.
    by rewrite /= !cctx_interp_cons IH assoc.
  Qed.

  Lemma cctx_interp_singleton tid qmax x :
    cctx_interp tid qmax [x] ≡ cctx_elt_interp tid qmax x.
  Proof. rewrite cctx_interp_cons cctx_interp_nil right_id //. Qed.

  Lemma fupd_cctx_interp tid qmax C :
    (|={⊤}=> cctx_interp tid qmax C) -∗ cctx_interp tid qmax C.
  Proof.
    rewrite /cctx_interp. iIntros "H". iIntros ([k L n T]) "%".
    iIntros (args) "HL HT". iMod "H".
    by iApply ("H" $! (k ◁cont(L, T)) with "[%] HL HT").
  Qed.

  Definition cctx_incl (E : elctx) (C1 C2 : cctx): Prop :=
    ∀ tid qmax, lft_ctx -∗ elctx_interp E -∗ cctx_interp tid qmax C1 -∗ cctx_interp tid qmax C2.

  Global Instance cctx_incl_preorder E : PreOrder (cctx_incl E).
  Proof.
    split.
    - iIntros (???) "_ _ $".
    - iIntros (??? H1 H2 ??) "#LFT #HE HC".
      iApply (H2 with "LFT HE"). by iApply (H1 with "LFT HE").
  Qed.

  Lemma incl_cctx_incl E C1 C2 : C1 ⊆ C2 → cctx_incl E C2 C1.
  Proof.
    rewrite /cctx_incl /cctx_interp. iIntros (HC1C2 tid ?) "_ #HE H * %".
    iApply ("H" with "[%]"). by apply HC1C2.
  Qed.

  Lemma cctx_incl_cons E k L n (T1 T2 : vec val n → tctx) C1 C2 :
    cctx_incl E C1 C2 → (∀ args, tctx_incl E L (T2 args) (T1 args)) →
    cctx_incl E (k ◁cont(L, T1) :: C1) (k ◁cont(L, T2) :: C2).
  Proof.
    iIntros (HC1C2 HT1T2 ??) "#LFT #HE H". rewrite /cctx_interp.
    iIntros (x) "Hin". iDestruct "Hin" as %[->|Hin]%elem_of_cons.
    - iIntros (args) "Htl HL HT".
      iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
      iMod (HT1T2 with "LFT HE HL HT") as "(HL & HT)".
      iDestruct ("HLclose" with "HL") as "HL".
      iApply ("H" $! (_ ◁cont(_, _)) with "[%] Htl HL HT").
      constructor.
    - iApply (HC1C2 with "LFT HE [H] [%]"); last done.
      iIntros (x') "%". iApply ("H" with "[%]"). by apply elem_of_cons; auto.
  Qed.

  Lemma cctx_incl_nil E C : cctx_incl E C [].
  Proof. apply incl_cctx_incl. by set_unfold. Qed.

  (* Extra strong cctx inclusion rule that we do not have on paper. *)
  Lemma cctx_incl_cons_dup E k L n (T1 T2 : vec val n → tctx) C1 C2 :
    k ◁cont(L, T1) ∈ C1 →
    (∀ args, tctx_incl E L (T2 args) (T1 args)) →
    cctx_incl E C1 C2 →
    cctx_incl E C1 (k ◁cont(L, T2) :: C2).
  Proof.
    intros Hin ??. rewrite <-cctx_incl_cons; try done.
    clear -Hin. iIntros (??) "_ #HE HC".
    rewrite cctx_interp_cons. iSplit; last done. clear -Hin.
    iInduction Hin as [] "IH"; rewrite cctx_interp_cons;
      [iDestruct "HC" as "[$ _]" | iApply "IH"; iDestruct "HC" as "[_ $]"].
  Qed.
End cont_context.

Hint Resolve cctx_incl_nil cctx_incl_cons : lrust_typing.
