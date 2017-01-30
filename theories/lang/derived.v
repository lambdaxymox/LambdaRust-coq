From lrust.lang Require Export lifting.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
Set Default Proof Using "Type".
Import uPred.

(** Define some derived forms, and derived lemmas about them. *)
Notation Lam xl e := (Rec BAnon xl e).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV xl e := (RecV BAnon xl e).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
Coercion lit_of_bool : bool >-> base_lit.
Notation If e0 e1 e2 := (Case e0 [e2;e1]).
Notation Newlft := (Lit LitUnit) (only parsing).
Notation Endlft := Skip (only parsing).

Section derived.
Context `{lrustG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind E f (el : list expr) (Ql : vec (val → iProp Σ) (length el)) vs Φ:
  is_Some (to_val f) →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf Hf]. revert vs Ql. induction el as [|e el IH]=>/= vs Ql; inv_vec Ql.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r big_sepL_nil.
      by iApply "H".
  - intros Q Ql. rewrite /= big_sepL_cons /=. iIntros "[He Hl] HΦ".
    assert (App f ((of_val <$> vs) ++ e :: el) = fill_item (AppRCtx vf vs el) e)
      as -> by rewrite /= (of_to_val f) //.
    iApply wp_bindi. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]) (of_to_val f) //.
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). rewrite /= big_sepL_cons. iFrame.
Qed.

Lemma wp_app_vec E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  is_Some (to_val f) →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hf). iApply (wp_app_ind _ _ _ _ []). done.
Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) E f el Φ :
  length Ql = length el → is_Some (to_val f) →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_of_list Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"); first done. iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite vec_to_list_length.
Qed.

(** Proof rules for the sugar *)
Lemma wp_lam E xl e eb e' el Φ :
  e = Lam xl eb →
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (xl +b+ []) eb →
  subst_l xl el eb = Some e' →
  ▷ WP e' @ E {{ Φ }} -∗ WP App e el @ E {{ Φ }}.
Proof.
  iIntros (-> ???) "?". iApply (wp_rec _ _ BAnon)=>//.
    by rewrite /= option_fmap_id.
Qed.

Lemma wp_let E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x e1 e2 @ E {{ Φ }} -∗ WP Let x e1 e2 @ E {{ Φ }}.
Proof. eauto using wp_lam. Qed.

Lemma wp_let' E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x (of_val v) e2 @ E {{ Φ }} -∗ WP Let x e1 e2 @ E {{ Φ }}.
Proof. intros ?. rewrite (of_to_val e1) //. eauto using wp_let. Qed.

Lemma wp_seq E e1 e2 v Φ :
  to_val e1 = Some v →
  Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} -∗ WP Seq e1 e2 @ E {{ Φ }}.
Proof. iIntros (??) "?". by iApply (wp_let _ BAnon). Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) -∗ WP Skip @ E {{ Φ }}.
Proof. iIntros. iApply wp_seq. done. iNext. by iApply wp_value. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P -∗ ▷ Φ (LitV true)) →
  (n2 < n1 → P -∗ ▷ Φ (LitV false)) →
  P -∗ WP BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl Hg) "HP".
  destruct (bool_decide_reflect (n1 ≤ n2)); [rewrite Hl //|rewrite Hg; last omega];
    clear Hl Hg; (iApply wp_bin_op_pure; first by econstructor); iNext; iIntros (?? Heval);
    inversion_clear Heval; [rewrite bool_decide_true //|rewrite bool_decide_false //].
Qed.

Lemma wp_eq_int E (n1 n2 : Z) P Φ :
  (n1 = n2 → P -∗ ▷ Φ (LitV true)) →
  (n1 ≠ n2 → P -∗ ▷ Φ (LitV false)) →
  P -∗ WP BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl Hg) "HP".
  destruct (bool_decide_reflect (n1 = n2)); [rewrite Hl //|rewrite Hg //];
    clear Hl Hg; iApply wp_bin_op_pure; subst.
  - intros. apply BinOpEqTrue. constructor.
  - iNext; iIntros (?? Heval). by inversion_clear Heval; inv_lit.
  - intros. apply BinOpEqFalse. by constructor.
  - iNext; iIntros (?? Heval). by inversion_clear Heval; inv_lit.
Qed.

(* TODO : wp_eq for locations, if needed. *)

Lemma wp_offset E l z Φ :
  ▷ Φ (LitV $ LitLoc $ shift_loc l z) -∗
    WP BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_plus E z1 z2 Φ :
  ▷ Φ (LitV $ LitInt $ z1 + z2) -∗
    WP BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_minus E z1 z2 Φ :
  ▷ Φ (LitV $ LitInt $ z1 - z2) -∗
    WP BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

(* TODO: Add lemmas for equality test. *)

Lemma wp_if E (b : bool) e1 e2 Φ :
  (if b then ▷ WP e1 @ E {{ Φ }} else ▷ WP e2 @ E {{ Φ }})%I -∗
  WP If (Lit b) e1 e2 @ E {{ Φ }}.
Proof. iIntros "?". by destruct b; iApply wp_case. Qed.
End derived.
