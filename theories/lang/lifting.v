From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang heap.
From lrust.lang Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class lrustG Σ := LRustG {
  lrustG_invG : invGS Σ;
  lrustG_gen_heapG :> heapGS Σ
}.

Instance lrustG_irisG `{!lrustG Σ} : irisGS lrust_lang Σ := {
  iris_invG := lrustG_invG;
  state_interp σ _ κs _ := heap_ctx σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
Global Opaque iris_invG.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

Local Hint Constructors head_step bin_op_eval lit_neq lit_eq : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section lifting.
Context `{!lrustG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : expr.
Implicit Types ef : option expr.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e :
  {{{ ▷ WP e {{ _, True }} }}} Fork e @ E {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ ? κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame.
  iModIntro. by iApply "HΦ".
Qed.

(** Pure reductions *)
Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; do 3 eexists; econstructor; simpl; eauto with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_head_step; inv_bin_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  eapply Forall_impl; [exact Hel|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2))) (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z  :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z)) (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1 (Case (Lit $ LitInt i) el) e | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

(** Heap *)
Lemma wp_alloc E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n') "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (heap_alloc with "Hσ") as "[Hσ Hl]"; [done..|].
  iModIntro; iSplit=> //. iFrame.
  iApply ("HΦ" $! _ (Z.to_nat n)). iFrame. iPureIntro. rewrite Z2Nat.id; lia.
Qed.

Lemma wp_free E (n:Z) l vl :
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n') "Hσ".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

Lemma wp_read_sc E l q v :
  {{{ ▷ l ↦{q} v }}} Read ScOrd (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (?) ">Hv HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[m ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_read_na E l q v :
  {{{ ▷ l ↦{q} v }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hv HΦ". iApply wp_lift_head_step; auto. iIntros (σ1 ? κ κs n) "Hσ".
  iMod (heap_read_na with "Hσ Hv") as (m) "(% & Hσ & Hσclose)".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1 n.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ' κs' n') "Hσ". iMod ("Hσclose" with "Hσ") as (n) "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "!>"; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. by iApply "HΦ".
Qed.

Lemma wp_write_sc E l e v v' :
  IntoVal e v →
  {{{ ▷ l ↦ v' }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iMod (heap_write _ _ _  v with "Hσ Hv") as "[Hσ Hv]".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_write_na E l e v v' :
  IntoVal e v →
  {{{ ▷ l ↦ v' }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ".
  iApply wp_lift_head_step; auto. iIntros (σ1 ? κ κs n) "Hσ".
  iMod (heap_write_na with "Hσ Hv") as "(% & Hσ & Hσclose)".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ' κs' n') "Hσ". iMod ("Hσclose" with "Hσ") as "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "!>"; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. by iApply "HΦ".
Qed.

Lemma wp_cas_int_fail E l q z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ ▷ l ↦{q} LitV (LitInt zl) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 0; l ↦{q} LitV (LitInt zl) }}}.
Proof.
  iIntros (<- ? Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[m ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; inv_lit.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ ▷ l ↦ LitV lit1 }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (<- ? Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct lit1; by eauto).
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; [inv_lit|].
  iMod (heap_write with "Hσ Hv") as "[$ Hv]".
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_int_suc E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitInt z1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma wp_cas_loc_suc E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitLoc l1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma wp_cas_loc_fail E l q q' q1 l1 v1' e2 lit2 l' vl' :
  IntoVal e2 (LitV lit2) → l1 ≠ l' →
  {{{ ▷ l ↦{q} LitV (LitLoc l') ∗ ▷ l' ↦{q'} vl' ∗ ▷ l1 ↦{q1} v1' }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 0);
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
Proof.
  iIntros (<- ? Φ) "(>Hl & >Hl' & >Hl1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ". iDestruct (heap_read with "Hσ Hl") as %[nl ?].
  iDestruct (heap_read with "Hσ Hl'") as %[nl' ?].
  iDestruct (heap_read with "Hσ Hl1") as %[nl1 ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; inv_lit.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; iFrame.
Qed.

Lemma wp_cas_loc_nondet E l l1 e2 l2 ll :
  IntoVal e2 (LitV $ LitLoc l2) →
  {{{ ▷ l ↦ LitV (LitLoc ll) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ b, RET LitV (lit_of_bool b);
      if b is true then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct (decide (ll = l1)) as [->|]; by eauto).
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; last lia.
  - inv_lit. iModIntro; iSplit; [done|]; iFrame "Hσ".
    iApply "HΦ"; simpl; auto.
  - iMod (heap_write with "Hσ Hv") as "[$ Hv]".
    iModIntro; iSplit; [done|]. iApply "HΦ"; iFrame.
Qed.

Lemma wp_eq_loc E (l1 : loc) (l2: loc) q1 q2 v1 v2 P Φ :
  (P -∗ ▷ l1 ↦{q1} v1) →
  (P -∗ ▷ l2 ↦{q2} v2) →
  (P -∗ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P -∗ WP BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost) "HP".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply wp_lift_pure_det_head_step_no_fork';
      [done|solve_exec_safe|solve_exec_puredet|].
    iApply wp_value. by iApply Hpost.
  - iApply wp_lift_atomic_head_step_no_fork; subst=>//.
    iIntros (σ1 ? κ κs n') "Hσ1". iModIntro. inv_head_step.
    iSplitR.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    (* We need to do a little gymnastics here to apply Hne now and strip away a
       ▷ but also have the ↦s. *)
    iAssert ((▷ ∃ q v, l1 ↦{q} v) ∧ (▷ ∃ q v, l2 ↦{q} v) ∧ ▷ Φ (LitV false))%I with "[HP]" as "HP".
    { iSplit; last iSplit.
      + iExists _, _. by iApply Hl1.
      + iExists _, _. by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 σ2 efs Hs) "!>".
    inv_head_step. iSplitR=>//. inv_bin_op_eval; inv_lit.
    + iExFalso. iDestruct "HP" as "[Hl1 _]".
      iDestruct "Hl1" as (??) "Hl1".
      iDestruct (heap_read σ2 with "Hσ1 Hl1") as %[??]; simplify_eq.
    + iExFalso. iDestruct "HP" as "[_ [Hl2 _]]".
      iDestruct "Hl2" as (??) "Hl2".
      iDestruct (heap_read σ2 with "Hσ1 Hl2") as %[??]; simplify_eq.
    + iDestruct "HP" as "[_ [_ $]]". done.
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind E f (el : list expr) (Ql : vec (val → iProp Σ) (length el)) vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el)) with (fill_item (AppRCtx vf vs el) e).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite vec_to_list_length.
Qed.
End lifting.
