From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import product.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeGS Σ}.

  Program Definition uninit_1 : type :=
    {| st_own tid vl := ⌜length vl = 1%nat⌝%I |}.
  Next Obligation. done. Qed.

  Global Instance uninit_1_send : Send uninit_1.
  Proof. iIntros (tid1 tid2 vl) "H". done. Qed.

  Definition uninit0 (n : nat) : type :=
    Π (replicate n uninit_1).

  Lemma uninit0_sz n : ty_size (uninit0 n) = n.
  Proof. induction n=>//=. by f_equal. Qed.

  Lemma uninit0_own n tid vl :
    ty_own (uninit0 n) tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof.
    iSplit.
    - iIntros "Hvl".
      iInduction n as [|n] "IH" forall (vl); simpl.
      + iDestruct "Hvl" as "%". subst vl. done.
      + iDestruct "Hvl" as (vl1 vl2) "(% & % & Hprod)".
        destruct vl1 as [|v [|]]; try done. subst vl. simpl.
        iDestruct ("IH" with "Hprod") as "%". iPureIntro. by f_equal.
    - iIntros "%". subst n. iInduction vl as [|v vl] "IH"; first done.
      simpl. iExists [v], vl. auto.
  Qed.

  (* We redefine uninit as an alias of uninit0, so that ty_size and ty_own
     compute directly.  We re-use the sharing from the product as that saves a whole
     lot of work. *)
  Program Definition uninit (n : nat) : type :=
    {| ty_size := n; ty_own tid vl := ⌜length vl = n⌝%I;
       ty_shr := (uninit0 n).(ty_shr) |}.
  Next Obligation. iIntros (???) "%". done. Qed.
  Next Obligation.
    iIntros (???????) "LFT Hvl". iApply (ty_share (uninit0 n) with "LFT"); first done.
    iApply (bor_iff with "[] Hvl"). iIntros "!> !>". setoid_rewrite uninit0_own.
    iSplit; iIntros; done.
  Qed.
  Next Obligation. intros. by apply ty_shr_mono. Qed.

  Global Instance uninit_wf n : TyWf (uninit n) :=
    { ty_lfts := []; ty_wf_E := [] }.

  Global Instance uninit_copy n : Copy (uninit n).
  Proof.
    assert (Copy (uninit0 n)) as [A B].
    { apply product_copy. by apply Forall_replicate, _. }
    split; first by apply _.
    rewrite uninit0_sz in B. setoid_rewrite uninit0_own in B. done.
  Qed.

  Global Instance uninit_send n : Send (uninit n).
  Proof. iIntros (???) "?". done. Qed.

  Global Instance uninit_sync n : Sync (uninit n).
  Proof. apply product_sync, Forall_replicate, _. Qed.

  (* Unfolding lemma, kep only for backwards compatibility. *)
  Lemma uninit_own n tid vl :
    (uninit n).(ty_own) tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof. done. Qed.

  Lemma uninit_uninit0_eqtype E L n :
    eqtype E L (uninit0 n) (uninit n).
  Proof.
    apply equiv_eqtype; constructor=>//=.
    - apply uninit0_sz.
    - iIntros (??). rewrite uninit0_own. done.
  Qed.

  Lemma uninit_product_subtype_cons_r {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    subtype E L (uninit ty.(ty_size)) ty →
    subtype E L (uninit (n-ty.(ty_size))) (Π tyl) →
    subtype E L (uninit n) (Π(ty :: tyl)).
  Proof.
    intros ?%Nat2Z.inj_le. rewrite -!uninit_uninit0_eqtype /uninit0=>Hty Htyl.
    rewrite (le_plus_minus ty.(ty_size) n) // replicate_plus
           -(prod_flatten_r _ _ [_]) /= -prod_app. repeat (done || f_equiv).
  Qed.
  Lemma uninit_product_subtype_cons_l {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    subtype E L ty (uninit ty.(ty_size)) →
    subtype E L (Π tyl) (uninit (n-ty.(ty_size))) →
    subtype E L (Π(ty :: tyl)) (uninit n).
  Proof.
    intros ?%Nat2Z.inj_le. rewrite -!uninit_uninit0_eqtype /uninit0=>Hty Htyl.
    rewrite (le_plus_minus ty.(ty_size) n) // replicate_plus
           -(prod_flatten_r _ _ [_]) /= -prod_app. repeat (done || f_equiv).
  Qed.
  Lemma uninit_product_eqtype_cons_r {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    eqtype E L (uninit ty.(ty_size)) ty →
    eqtype E L (uninit (n-ty.(ty_size))) (Π tyl) →
    eqtype E L (uninit n) (Π(ty :: tyl)).
  Proof.
    intros ? [] []. split.
    - by apply uninit_product_subtype_cons_r.
    - by apply uninit_product_subtype_cons_l.
  Qed.
  Lemma uninit_product_eqtype_cons_l {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    eqtype E L ty (uninit ty.(ty_size)) →
    eqtype E L (Π tyl) (uninit (n-ty.(ty_size))) →
    eqtype E L (Π(ty :: tyl)) (uninit n).
  Proof. symmetry. by apply uninit_product_eqtype_cons_r. Qed.

  Lemma uninit_unit_eqtype E L n :
    n = 0%nat →
    eqtype E L (uninit n) unit.
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
  Lemma uninit_unit_eqtype' E L n :
    n = 0%nat →
    eqtype E L unit (uninit n).
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
  Lemma uninit_unit_subtype E L n :
    n = 0%nat →
    subtype E L (uninit n) unit.
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
  Lemma uninit_unit_subtype' E L n :
    n = 0%nat →
    subtype E L unit (uninit n).
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
End uninit.

Global Hint Resolve uninit_product_eqtype_cons_l uninit_product_eqtype_cons_r
             uninit_product_subtype_cons_l uninit_product_subtype_cons_r
             uninit_unit_eqtype uninit_unit_eqtype'
             uninit_unit_subtype uninit_unit_subtype' : lrust_typing.
