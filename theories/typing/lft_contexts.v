From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export base.
From lrust.lifetime Require Import frac_borrow.
Set Default Proof Using "Type".

Definition elctx_elt : Type := lft * lft.
Notation elctx := (list elctx_elt).

Declare Scope lrust_elctx_scope.
Delimit Scope lrust_elctx_scope with EL.
(* We need to define [elctx] and [llctx] as notations to make eauto
   work. But then, Coq is not able to bind them to their
   notations, so we have to use [Arguments] everywhere. *)
Bind Scope lrust_elctx_scope with elctx_elt.

Notation "κ1 ⊑ₑ κ2" := (@pair lft lft κ1 κ2) (at level 70).

Definition llctx_elt : Type := lft * list lft.
Notation llctx := (list llctx_elt).

Notation "κ ⊑ₗ κl" := (@pair lft (list lft) κ κl) (at level 70).

Section lft_contexts.
  Context `{!invGS Σ, !lftG Σ lft_userE}.
  Implicit Type (κ : lft).

  (* External lifetime contexts. *)
  Definition elctx_elt_interp (x : elctx_elt) : iProp Σ :=
    ⌜(x.1 ⊑ˢʸⁿ x.2)⌝%I.

  Definition elctx_interp (E : elctx) : iProp Σ :=
    ([∗ list] x ∈ E, elctx_elt_interp x)%I.
  Global Instance elctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) elctx_interp.
  Proof. intros ???. by apply big_opL_permutation. Qed.
  Global Instance elctx_interp_persistent E :
    Persistent (elctx_interp E).
  Proof. apply _. Qed.

  (* Local lifetime contexts. *)
  (* To support [type_call_iris'], the local lifetime [x.1] may be an
  intersection of not just the atomic lifetime [κ0] but also of some extra
  lifetimes [κextra], of which a smaller fraction [qextra] is owned (multiplied
  by [q] to remain fractional). Since [x.2] is empty, [type_call_iris'] can show
  that [κ0 ⊓ κextra] is the same after execution the function as it was before,
  which is sufficient to extract the lifetime tokens for [κextra] again. *)
  Definition llctx_elt_interp (qmax : Qp) (x : llctx_elt) : iProp Σ :=
    let κ' := lft_intersect_list (x.2) in
    (* This is [qeff := min 1 qmax], i.e., we cap qmax at [1] -- but the old
    std++ we use here does not yet have [min] on [Qp].
    We do the cap so that we never need to have more than [1] of this token. *)
    let qeff := (if decide (1 ≤ qmax) then 1 else qmax)%Qp in
    (∃ κ0, ⌜x.1 = κ' ⊓ κ0⌝ ∗ qeff.[κ0] ∗ (qeff.[κ0] ={↑lftN ∪ lft_userE}[lft_userE]▷=∗ [†κ0]))%I.
  (* Local lifetime contexts without the "ending a lifetime" viewshifts -- these
  are fractional. *)
  Definition llctx_elt_interp_noend (qmax : Qp) (x : llctx_elt) (q : Qp) : iProp Σ :=
    let κ' := lft_intersect_list (x.2) in
    let qeff := (if decide (1 ≤ qmax) then 1 else qmax)%Qp in
    (∃ κ0, ⌜x.1 = κ' ⊓ κ0⌝ ∗ (qeff * q).[κ0])%I.
  Global Instance llctx_elt_interp_noend_fractional qmax x :
    Fractional (llctx_elt_interp_noend qmax x).
  Proof.
    destruct x as [κ κs]. iIntros (q q'). iSplit; iIntros "H".
    - iDestruct "H" as (κ0) "(% & Hq)".
      rewrite Qp_mul_add_distr_l.
      iDestruct "Hq" as "[Hq Hq']".
      iSplitL "Hq"; iExists _; by iFrame "∗%".
    - iDestruct "H" as "[Hq Hq']".
      iDestruct "Hq" as (κ0) "(% & Hq)".
      iDestruct "Hq'" as (κ0') "(% & Hq')". simpl in *.
      rewrite (inj ((lft_intersect_list κs) ⊓.) κ0' κ0); last congruence.
      iExists κ0. rewrite Qp_mul_add_distr_l. by iFrame "∗%".
  Qed.

  Lemma llctx_elt_interp_acc_noend qmax x :
    llctx_elt_interp qmax x -∗
    llctx_elt_interp_noend qmax x 1 ∗ (llctx_elt_interp_noend qmax x 1 -∗ llctx_elt_interp qmax x).
  Proof.
    destruct x as [κ κs].
    iIntros "H". iDestruct "H" as (κ0) "(% & Hq & Hend)". iSplitL "Hq".
    { iExists κ0. rewrite Qp_mul_1_r. by iFrame "∗%". }
    iIntros "H". iDestruct "H" as (κ0') "(% & Hq')". simpl in *.
    rewrite (inj ((lft_intersect_list κs) ⊓.) κ0' κ0); last congruence.
    iExists κ0. rewrite Qp_mul_1_r. by iFrame "∗%".
  Qed.

  Definition llctx_interp (qmax : Qp) (L : llctx) : iProp Σ :=
    ([∗ list] x ∈ L, llctx_elt_interp qmax x)%I.
  Definition llctx_interp_noend (qmax : Qp) (L : llctx) (q : Qp) : iProp Σ :=
    ([∗ list] x ∈ L, llctx_elt_interp_noend qmax x q)%I.
  Global Instance llctx_interp_fractional qmax L :
    Fractional (llctx_interp_noend qmax L).
  Proof. intros ??. rewrite -big_sepL_sep. by setoid_rewrite <-fractional. Qed.
  Global Instance llctx_interp_as_fractional qmax L q :
    AsFractional (llctx_interp_noend qmax L q) (llctx_interp_noend qmax L) q.
  Proof. split; first done. apply _. Qed.
  Global Instance llctx_interp_permut qmax :
    Proper ((≡ₚ) ==> (⊣⊢)) (llctx_interp qmax).
  Proof. intros ???. by apply big_opL_permutation. Qed.

  Lemma llctx_interp_acc_noend qmax L :
    llctx_interp qmax L -∗
    llctx_interp_noend qmax L 1 ∗ (llctx_interp_noend qmax L 1 -∗ llctx_interp qmax L).
  Proof.
    rewrite /llctx_interp. setoid_rewrite llctx_elt_interp_acc_noend at 1.
    rewrite big_sepL_sep. iIntros "[$ Hclose]". iIntros "Hnoend".
    iCombine "Hclose Hnoend" as "H".
    rewrite /llctx_interp_noend -big_sepL_sep.
    setoid_rewrite bi.wand_elim_l. done.
  Qed.

  Lemma lctx_equalize_lft_sem qmax κ1 κ2 `{!frac_borG Σ} :
    lft_ctx -∗ llctx_elt_interp qmax (κ1 ⊑ₗ [κ2]%list) ={⊤}=∗
      κ1 ⊑ κ2 ∗ κ2 ⊑ κ1.
  Proof.
    iIntros "#LFT". iDestruct 1 as (κ) "(% & Hκ & _)"; simplify_eq/=.
    iMod (lft_eternalize with "Hκ") as "#Hincl".
    iModIntro. iSplit.
    - iApply lft_incl_trans; iApply lft_intersect_incl_l.
    - iApply (lft_incl_glb with "[]"); first iApply (lft_incl_glb with "[]").
      + iApply lft_incl_refl.
      + iApply lft_incl_static.
      + iApply lft_incl_trans; last done. iApply lft_incl_static.
  Qed.
  Lemma lctx_equalize_lft_sem_static qmax κ `{!frac_borG Σ} :
    lft_ctx -∗ llctx_elt_interp qmax (κ ⊑ₗ []%list) ={⊤}=∗
      static ⊑ κ.
  Proof.
    iIntros "#LFT". iDestruct 1 as (κ') "(% & Hκ & _)"; simplify_eq/=.
    iMod (lft_eternalize with "Hκ") as "#Hincl".
    iModIntro.
    - iApply (lft_incl_glb with "[]"); simpl.
      + iApply lft_incl_refl.
      + done.
  Qed.

  (* Lifetime inclusion *)
  Context (E : elctx) (L : llctx).

  Definition lctx_lft_incl κ κ' : Prop :=
    ∀ qmax qL, llctx_interp_noend qmax L qL -∗ □ (elctx_interp E -∗ ⌜κ ⊑ˢʸⁿ κ'⌝)%I.

  Definition lctx_lft_eq κ κ' : Prop :=
    lctx_lft_incl κ κ' ∧ lctx_lft_incl κ' κ.

  Lemma lctx_lft_incl_incl_noend κ κ' : lctx_lft_incl κ κ' → lctx_lft_incl κ κ'.
  Proof. done. Qed.
  Lemma lctx_lft_incl_incl κ κ' qmax :
    lctx_lft_incl κ κ' → llctx_interp qmax L -∗ □ (elctx_interp E -∗ ⌜κ ⊑ˢʸⁿ κ'⌝)%I.
  Proof.
    iIntros (Hincl) "HL".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL _]".
    iApply Hincl. done.
  Qed.

  Lemma lctx_lft_incl_refl κ : lctx_lft_incl κ κ.
  Proof.
    iIntros (qmax qL) "_ !> _".
    iPureIntro. apply lft_incl_syn_refl.
  Qed.

  Global Instance lctx_lft_incl_preorder : PreOrder lctx_lft_incl.
  Proof.
    split; first by intros ?; apply lctx_lft_incl_refl.
    iIntros (??? H1 H2 ??) "HL".
    iDestruct (H1 with "HL") as "#H1".
    iDestruct (H2 with "HL") as "#H2".
    iClear "∗". iIntros "!> #HE".
    iDestruct ("H1" with "HE") as "%". iDestruct ("H2" with "HE") as "%".
    iPureIntro.
    by eapply lft_incl_syn_trans.
  Qed.

  Global Instance lctx_lft_incl_proper :
    Proper (lctx_lft_eq ==> lctx_lft_eq ==> iff) lctx_lft_incl.
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance lctx_lft_eq_equivalence : Equivalence lctx_lft_eq.
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma lctx_lft_incl_static κ : lctx_lft_incl κ static.
  Proof. iIntros (qmax qL) "_ !> _". iPureIntro. apply lft_incl_syn_static. Qed.

  Lemma lctx_lft_incl_local κ κ' κs :
    κ ⊑ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    iIntros (? Hκ'κs qmax qL) "H".
    iDestruct (big_sepL_elem_of with "H") as "H"; first done.
    iDestruct "H" as (κ'') "[EQ _]". iDestruct "EQ" as %EQ.
    simpl in EQ; subst. iIntros "!> #HE".
    iPureIntro.
    eapply lft_incl_syn_trans; first apply lft_intersect_incl_syn_l.
    by apply lft_intersect_list_elem_of_incl_syn.
  Qed.

  Lemma lctx_lft_incl_local' κ κ' κ'' κs :
    κ ⊑ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local. Qed.

  Lemma lctx_lft_incl_external κ κ' : κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ κ'.
  Proof.
    iIntros (???) "_ !> #HE".
    rewrite /elctx_interp /elctx_elt_interp big_sepL_elem_of //. done.
  Qed.

  Lemma lctx_lft_incl_external' κ κ' κ'' :
    κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_external. Qed.

  Lemma lctx_lft_incl_intersect κ κ' κ'' :
    lctx_lft_incl κ κ' → lctx_lft_incl κ κ'' →
    lctx_lft_incl (κ ⊓ κ) (κ' ⊓ κ'').
  Proof.
    iIntros (Hκ' Hκ'' ??) "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iDestruct (Hκ'' with "HL") as "#Hκ''".
    iIntros "!> #HE".
    iDestruct ("Hκ'" with "HE") as "%".
    iDestruct ("Hκ''" with "HE") as "%".
    iPureIntro.
    by apply lft_intersect_mono_syn.
  Qed.

  Lemma lctx_lft_incl_intersect_l κ κ' κ'' :
    lctx_lft_incl κ κ' →
    lctx_lft_incl (κ ⊓ κ'') κ'.
  Proof.
    iIntros (Hκ' ??) "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iDestruct ("Hκ'" with "HE") as "%". iPureIntro.
    eapply lft_incl_syn_trans; last eassumption.
    by apply lft_intersect_incl_syn_l.
  Qed.

  Lemma lctx_lft_incl_intersect_r κ κ' κ'' :
    lctx_lft_incl κ κ' →
    lctx_lft_incl (κ'' ⊓ κ) κ'.
  Proof.
    iIntros (Hκ' ??) "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iDestruct ("Hκ'" with "HE") as "%". iPureIntro.
    eapply lft_incl_syn_trans; last eassumption.
    by apply lft_intersect_incl_syn_r.
  Qed.

  (* Lifetime aliveness *)

  Definition lctx_lft_alive (κ : lft) : Prop :=
    ∀ F qmax qL, ↑lftN ⊆ F → elctx_interp E -∗ llctx_interp_noend qmax L qL ={F}=∗
          ∃ q', q'.[κ] ∗ (q'.[κ] ={F}=∗ llctx_interp_noend qmax L qL).

  Lemma lctx_lft_alive_tok_noend κ F qmax q :
    ↑lftN ⊆ F →
    lctx_lft_alive κ → elctx_interp E -∗ llctx_interp_noend qmax L q ={F}=∗
      ∃ q', q'.[κ] ∗ llctx_interp_noend qmax L q' ∗
                   (q'.[κ] -∗ llctx_interp_noend qmax L q' ={F}=∗ llctx_interp_noend qmax L q).
  Proof.
    iIntros (? Hal) "#HE [HL1 HL2]".
    iMod (Hal with "HE HL1") as (q') "[Htok Hclose]"; first done.
    destruct (Qp_lower_bound (q/2) q') as (qq & q0  & q'0 & Hq & ->). rewrite Hq.
    iExists qq. iDestruct "HL2" as "[$ HL]". iDestruct "Htok" as "[$ Htok]".
    iIntros "!> Htok' HL'". iCombine "HL'" "HL" as "HL". rewrite -Hq. iFrame.
    iApply "Hclose". iFrame.
  Qed.

  Lemma lctx_lft_alive_tok κ F qmax :
    ↑lftN ⊆ F →
    lctx_lft_alive κ → elctx_interp E -∗ llctx_interp qmax L ={F}=∗
      ∃ q', q'.[κ] ∗ llctx_interp_noend qmax L q' ∗
                   (q'.[κ] -∗ llctx_interp_noend qmax L q' ={F}=∗ llctx_interp qmax L).
  Proof.
    iIntros (? Hal) "#HE HL".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (lctx_lft_alive_tok_noend with "HE HL") as (q') "(Hκ & HL & Hclose)"; [done..|].
    iModIntro. iExists q'. iFrame. iIntros "Hκ HL".
    iApply "HLclose". iApply ("Hclose" with "Hκ"). done.
  Qed.

  Lemma lctx_lft_alive_tok_noend_list κs F qmax q :
    ↑lftN ⊆ F → Forall lctx_lft_alive κs →
      elctx_interp E -∗ llctx_interp_noend qmax L q ={F}=∗
         ∃ q', q'.[lft_intersect_list κs] ∗ llctx_interp_noend qmax L q' ∗
                   (q'.[lft_intersect_list κs] -∗ llctx_interp_noend qmax L q' ={F}=∗ llctx_interp_noend qmax L q).
  Proof.
    iIntros (? Hκs) "#HE". iInduction κs as [|κ κs] "IH" forall (q Hκs).
    { iIntros "HL !>". iExists _. iFrame "HL". iSplitL; first iApply lft_tok_static.
      iIntros "_ $". done. }
    inversion_clear Hκs.
    iIntros "HL". iMod (lctx_lft_alive_tok_noend κ with "HE HL")as (q') "(Hκ & HL & Hclose1)"; [solve_typing..|].
    iMod ("IH" with "[//] HL") as (q'') "(Hκs & HL & Hclose2)".
    destruct (Qp_lower_bound q' q'') as (qq & q0  & q'0 & -> & ->).
    iExists qq. iDestruct "HL" as "[$ HL2]". iDestruct "Hκ" as "[Hκ1 Hκ2]".
    iDestruct "Hκs" as "[Hκs1 Hκs2]". iModIntro. simpl. rewrite -lft_tok_sep. iSplitL "Hκ1 Hκs1".
    { by iFrame. }
    iIntros "[Hκ1 Hκs1] HL1". iMod ("Hclose2" with "[$Hκs1 $Hκs2] [$HL1 $HL2]") as "HL".
    iMod ("Hclose1" with "[$Hκ1 $Hκ2] HL") as "HL". done.
  Qed.

  Lemma lctx_lft_alive_tok_list κs F qmax :
    ↑lftN ⊆ F → Forall lctx_lft_alive κs →
      elctx_interp E -∗ llctx_interp qmax L ={F}=∗
         ∃ q', q'.[lft_intersect_list κs] ∗ llctx_interp_noend qmax L q' ∗
                   (q'.[lft_intersect_list κs] -∗ llctx_interp_noend qmax L q' ={F}=∗ llctx_interp qmax L).
  Proof.
    iIntros (? Hal) "#HE HL".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (lctx_lft_alive_tok_noend_list with "HE HL") as (q') "(Hκ & HL & Hclose)"; [done..|].
    iModIntro. iExists q'. iFrame. iIntros "Hκ HL".
    iApply "HLclose". iApply ("Hclose" with "Hκ"). done.
  Qed.

  Lemma lctx_lft_alive_static : lctx_lft_alive static.
  Proof.
    iIntros (F qmax qL ?) "_ $". iExists 1%Qp. iSplitL; last by auto.
    by iApply lft_tok_static.
  Qed.

  Lemma lctx_lft_alive_local κ κs:
    κ ⊑ₗ κs ∈ L → Forall lctx_lft_alive κs → lctx_lft_alive κ.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs F qmax qL ?) "#HE HL".
    iDestruct "HL" as "[HL1 HL2]". rewrite {2}/llctx_interp_noend /llctx_elt_interp.
    iDestruct (big_sepL_lookup_acc with "HL2") as "[Hκ Hclose]"; first done.
    iDestruct "Hκ" as (κ0) "(EQ & Htok)". simpl. iDestruct "EQ" as %->.
    iAssert (∃ q', q'.[lft_intersect_list κs] ∗
      (q'.[lft_intersect_list κs] ={F}=∗ llctx_interp_noend qmax L (qL / 2)))%I
      with "[> HE HL1]" as "H".
    { move:(qL/2)%Qp=>qL'. clear HL.
      iInduction Hκs as [|κ κs Hκ ?] "IH" forall (qL').
      - iExists 1%Qp. iFrame. iSplitR; last by auto. iApply lft_tok_static.
      - iDestruct "HL1" as "[HL1 HL2]".
        iMod (Hκ with "HE HL1") as (q') "[Htok' Hclose]"; first done.
        iMod ("IH" with "HL2") as (q'') "[Htok'' Hclose']".
        destruct (Qp_lower_bound q' q'') as (q0 & q'2 & q''2 & -> & ->).
        iExists q0. rewrite -lft_tok_sep. iDestruct "Htok'" as "[$ Hr']".
        iDestruct "Htok''" as "[$ Hr'']". iIntros "!>[Hκ Hfold]".
        iMod ("Hclose" with "[$Hκ $Hr']") as "$". iApply "Hclose'". iFrame. }
    iDestruct "H" as (q') "[Htok' Hclose']". rewrite -{5}(Qp_div_2 qL).
    set (qeff := (if decide (1 ≤ qmax) then 1 else qmax)%Qp).
    destruct (Qp_lower_bound q' (qeff * (qL/2))) as (q0 & q'2 & q''2 & -> & Hmax).
    iExists q0. rewrite -(lft_tok_sep q0). rewrite Hmax.
    iDestruct "Htok" as "[$ Htok]".
    iDestruct "Htok'" as "[$ Htok']". iIntros "!>[Hfold Hκ0]".
    iMod ("Hclose'" with "[$Hfold $Htok']") as "$".
    rewrite /llctx_interp /llctx_elt_interp. iApply "Hclose".
    iExists κ0. rewrite Hmax. iFrame. auto.
  Qed.

  Lemma lctx_lft_alive_incl κ κ':
    lctx_lft_alive κ → lctx_lft_incl κ κ' → lctx_lft_alive κ'.
  Proof.
    iIntros (Hal Hinc F qmax qL ?) "#HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl".
    { rewrite Hinc. iDestruct ("HL" with "HE") as "%".
      by iApply lft_incl_syn_sem. }
    iMod (Hal with "HE HL") as (q') "[Htok Hclose]"; first done.
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose']"; first done.
    iExists q''. iIntros "{$Htok}!>Htok". iApply ("Hclose" with "[> -]").
    by iApply "Hclose'".
  Qed.

  Lemma lctx_lft_alive_external κ κ':
    κ ⊑ₑ κ' ∈ E → lctx_lft_alive κ → lctx_lft_alive κ'.
  Proof.
    intros. by eapply lctx_lft_alive_incl, lctx_lft_incl_external.
  Qed.

  (* External lifetime context satisfiability *)

  Definition elctx_sat E' : Prop :=
    ∀ qmax qL, llctx_interp_noend qmax L qL -∗ □ (elctx_interp E -∗ elctx_interp E').

  Lemma elctx_sat_nil : elctx_sat [].
  Proof. iIntros (??) "_ !> _". by rewrite /elctx_interp /=. Qed.

  Lemma elctx_sat_lft_incl E' κ κ' :
    lctx_lft_incl κ κ' → elctx_sat E' → elctx_sat ((κ ⊑ₑ κ') :: E').
  Proof.
    iIntros (Hκκ' HE' qmax qL) "HL".
    iDestruct (Hκκ' with "HL") as "#Hincl".
    iDestruct (HE' with "HL") as "#HE'".
    iClear "∗". iIntros "!> #HE". iSplit.
    - by iApply "Hincl".
    - by iApply "HE'".
  Qed.

  Lemma elctx_sat_app E1 E2 :
    elctx_sat E1 → elctx_sat E2 → elctx_sat (E1 ++ E2).
  Proof.
    iIntros (HE1 HE2 ??) "HL".
    iDestruct (HE1 with "HL") as "#HE1".
    iDestruct (HE2 with "HL") as "#HE2".
    iClear "∗". iIntros "!> #HE".
    iDestruct ("HE1" with "HE") as "#$".
    iApply ("HE2" with "HE").
  Qed.

  Lemma elctx_sat_refl : elctx_sat E.
  Proof. iIntros (??) "_ !> ?". done. Qed.
End lft_contexts.

Arguments lctx_lft_incl {_ _} _ _ _ _.
Arguments lctx_lft_eq {_ _} _ _ _ _.
Arguments lctx_lft_alive {_ _ _} _ _ _.
Arguments elctx_sat {_ _} _ _ _.
Arguments lctx_lft_incl_incl {_ _ _ _ _} _ _.
Arguments lctx_lft_incl_incl_noend {_ _ _ _} _ _.
Arguments lctx_lft_alive_tok {_ _ _ _ _} _ _ _.
Arguments lctx_lft_alive_tok_noend {_ _ _ _ _} _ _ _.

Lemma elctx_sat_submseteq `{!invGS Σ, !lftG Σ lft_userE} E E' L :
  E' ⊆+ E → elctx_sat E L E'.
Proof. iIntros (HE' ??) "_ !> H". by iApply big_sepL_submseteq. Qed.

Global Hint Resolve
     lctx_lft_incl_refl lctx_lft_incl_static lctx_lft_incl_local'
     lctx_lft_incl_external' lctx_lft_incl_intersect
     lctx_lft_incl_intersect_l lctx_lft_incl_intersect_r
     lctx_lft_alive_static lctx_lft_alive_local lctx_lft_alive_external
     elctx_sat_nil elctx_sat_lft_incl elctx_sat_app elctx_sat_refl
  : lrust_typing.

Global Hint Extern 10 (lctx_lft_eq _ _ _ _) => split : lrust_typing.

Global Hint Resolve elctx_sat_submseteq | 100 : lrust_typing.

Global Hint Opaque elctx_sat lctx_lft_alive lctx_lft_incl : lrust_typing.
