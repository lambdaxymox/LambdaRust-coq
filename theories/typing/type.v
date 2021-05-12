From iris.algebra Require Import numbers.
From iris.base_logic.lib Require Export na_invariants.
From lrust.lang Require Export proofmode notation.
From lrust.lifetime Require Export frac_borrow.
From lrust.typing Require Export base.
From lrust.typing Require Import lft_contexts.
Set Default Proof Using "Type".

Class typeG Σ := TypeG {
  type_lrustG :> lrustG Σ;
  type_lftG :> lftG Σ;
  type_na_invG :> na_invG Σ;
  type_frac_borrowG :> frac_borG Σ
}.

Definition lrustN := nroot .@ "lrust".
Definition shrN  := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

Record type `{!typeG Σ} :=
  { ty_size : nat;
    ty_own : thread_id → list val → iProp Σ;
    ty_shr : lft → thread_id → loc → iProp Σ;

    ty_shr_persistent κ tid l : Persistent (ty_shr κ tid l);

    ty_size_eq tid vl : ty_own tid vl -∗ ⌜length vl = ty_size⌝;
    (* The mask for starting the sharing does /not/ include the
       namespace N, for allowing more flexibility for the user of
       this type (typically for the [own] type). AFAIK, there is no
       fundamental reason for this.
       This should not be harmful, since sharing typically creates
       invariants, which does not need the mask.  Moreover, it is
       more consistent with thread-local tokens, which we do not
       give any.

       The lifetime token is needed (a) to make the definition of simple types
       nicer (they would otherwise require a "∨ □|=>[†κ]"), and (b) so that
       we can have emp == sum [].
     *)
    ty_share E κ l tid q : ↑lftN ⊆ E →
      lft_ctx -∗ &{κ} (l ↦∗: ty_own tid) -∗ q.[κ] ={E}=∗
      ty_shr κ tid l ∗ q.[κ];
    ty_shr_mono κ κ' tid l :
      κ' ⊑ κ -∗ ty_shr κ tid l -∗ ty_shr κ' tid l
  }.
Existing Instance ty_shr_persistent.
Instance: Params (@ty_size) 2 := {}.
Instance: Params (@ty_own) 2 := {}.
Instance: Params (@ty_shr) 2 := {}.

Arguments ty_own {_ _} !_ _ _ / : simpl nomatch.

Class TyWf `{!typeG Σ} (ty : type) := { ty_lfts : list lft; ty_wf_E : elctx }.
Arguments ty_lfts {_ _} _ {_}.
Arguments ty_wf_E {_ _} _ {_}.

Definition ty_outlives_E `{!typeG Σ} ty `{!TyWf ty} (κ : lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlives_E_elctx_sat `{!typeG Σ} E L ty `{!TyWf ty} α β :
  ty_outlives_E ty β ⊆+ E →
  lctx_lft_incl E L α β →
  elctx_sat E L (ty_outlives_E ty α).
Proof.
  unfold ty_outlives_E. induction ty.(ty_lfts) as [|κ l IH]=>/= Hsub Hαβ.
  - solve_typing.
  - apply elctx_sat_lft_incl.
    + etrans; first done. eapply lctx_lft_incl_external, elem_of_submseteq, Hsub.
      set_solver.
    + apply IH, Hαβ. etrans; last done. by apply submseteq_cons.
Qed.

(* Lift TyWf to lists.  We cannot use `Forall` because that one is restricted to Prop. *)
Inductive TyWfLst `{!typeG Σ} : list type → Type :=
| tyl_wf_nil : TyWfLst []
| tyl_wf_cons ty tyl `{!TyWf ty, !TyWfLst tyl} : TyWfLst (ty::tyl).
Existing Class TyWfLst.
Existing Instances tyl_wf_nil tyl_wf_cons.

Fixpoint tyl_lfts `{!typeG Σ} tyl {WF : TyWfLst tyl} : list lft :=
  match WF with
  | tyl_wf_nil => []
  | tyl_wf_cons ty [] => ty.(ty_lfts)
  | tyl_wf_cons ty tyl => ty.(ty_lfts) ++ tyl.(tyl_lfts)
  end.

Fixpoint tyl_wf_E `{!typeG Σ} tyl {WF : TyWfLst tyl} : elctx :=
  match WF with
  | tyl_wf_nil => []
  | tyl_wf_cons ty [] => ty.(ty_wf_E)
  | tyl_wf_cons ty tyl => ty.(ty_wf_E) ++ tyl.(tyl_wf_E)
  end.

Fixpoint tyl_outlives_E `{!typeG Σ} tyl {WF : TyWfLst tyl} (κ : lft) : elctx :=
  match WF with
  | tyl_wf_nil => []
  | tyl_wf_cons ty [] => ty_outlives_E ty κ
  | tyl_wf_cons ty tyl => ty_outlives_E ty κ ++ tyl.(tyl_outlives_E) κ
  end.

Lemma tyl_outlives_E_elctx_sat `{!typeG Σ} E L tyl {WF : TyWfLst tyl} α β :
  tyl_outlives_E tyl β ⊆+ E →
  lctx_lft_incl E L α β →
  elctx_sat E L (tyl_outlives_E tyl α).
Proof.
  induction WF as [|? [] ?? IH]=>/=.
  - solve_typing.
  - intros. by eapply ty_outlives_E_elctx_sat.
  - intros. apply elctx_sat_app, IH; [eapply ty_outlives_E_elctx_sat| |]=>//;
      (etrans; [|done]); solve_typing.
Qed.

Record simple_type `{!typeG Σ} :=
  { st_own : thread_id → list val → iProp Σ;
    st_size_eq tid vl : st_own tid vl -∗ ⌜length vl = 1%nat⌝;
    st_own_persistent tid vl : Persistent (st_own tid vl) }.
Existing Instance st_own_persistent.
Instance: Params (@st_own) 2 := {}.

Program Definition ty_of_st `{!typeG Σ} (st : simple_type) : type :=
  {| ty_size := 1; ty_own := st.(st_own);
     (* [st.(st_own) tid vl] needs to be outside of the fractured
         borrow, otherwise I do not know how to prove the shr part of
         [subtype_shr_mono]. *)
     ty_shr := λ κ tid l,
               (∃ vl, &frac{κ} (λ q, l ↦∗{q} vl) ∗ ▷ st.(st_own) tid vl)%I
  |}.
Next Obligation. intros. apply st_size_eq. Qed.
Next Obligation.
  iIntros (?? st E κ l tid ??) "#LFT Hmt Hκ".
  iMod (bor_exists with "LFT Hmt") as (vl) "Hmt"; first solve_ndisj.
  iMod (bor_sep with "LFT Hmt") as "[Hmt Hown]"; first solve_ndisj.
  iMod (bor_persistent with "LFT Hown Hκ") as "[Hown $]"; first solve_ndisj.
  iMod (bor_fracture with "LFT [Hmt]") as "Hfrac"; by eauto with iFrame.
Qed.
Next Obligation.
  iIntros (?? st κ κ' tid l) "#Hord H".
  iDestruct "H" as (vl) "[#Hf #Hown]".
  iExists vl. iFrame "Hown". by iApply (frac_bor_shorten with "Hord").
Qed.

Coercion ty_of_st : simple_type >-> type.

Declare Scope lrust_type_scope.
Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(* OFE and COFE structures on types and simple types. *)
Section ofe.
  Context `{!typeG Σ}.

  Inductive type_equiv' (ty1 ty2 : type) : Prop :=
    Type_equiv :
      ty1.(ty_size) = ty2.(ty_size) →
      (∀ tid vs, ty1.(ty_own) tid vs ≡ ty2.(ty_own) tid vs) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡ ty2.(ty_shr) κ tid l) →
      type_equiv' ty1 ty2.
  Instance type_equiv : Equiv type := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type) : Prop :=
    Type_dist :
      ty1.(ty_size) = ty2.(ty_size) →
      (∀ tid vs, ty1.(ty_own) tid vs ≡{n}≡ ty2.(ty_own) tid vs) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n}≡ ty2.(ty_shr) κ tid l) →
      type_dist' n ty1 ty2.
  Instance type_dist : Dist type := type_dist'.

  Let T := prodO
    (prodO natO (thread_id -d> list val -d> iPropO Σ))
    (lft -d> thread_id -d> loc -d> iPropO Σ).
  Let P (x : T) : Prop :=
    (∀ κ tid l, Persistent (x.2 κ tid l)) ∧
    (∀ tid vl, x.1.2 tid vl -∗ ⌜length vl = x.1.1⌝) ∧
    (∀ E κ l tid q, ↑lftN ⊆ E →
      lft_ctx -∗ &{κ} (l ↦∗: λ vs, x.1.2 tid vs) -∗
      q.[κ] ={E}=∗ x.2 κ tid l ∗ q.[κ]) ∧
    (∀ κ κ' tid l, κ' ⊑ κ -∗ x.2 κ tid l -∗ x.2 κ' tid l).

  Definition type_unpack (ty : type) : T :=
    (ty.(ty_size), λ tid vl, (ty.(ty_own) tid vl), ty.(ty_shr)).
  Program Definition type_pack (x : T) (H : P x) : type :=
    {| ty_size := x.1.1; ty_own tid vl := x.1.2 tid vl; ty_shr := x.2 |}.
  Solve Obligations with by intros [[??] ?] (?&?&?&?).

  Definition type_ofe_mixin : OfeMixin type.
  Proof.
    apply (iso_ofe_mixin type_unpack).
    - split; [by destruct 1|by intros [[??] ?]; constructor].
    - split; [by destruct 1|by intros [[??] ?]; constructor].
  Qed.
  Canonical Structure typeO : ofe := Ofe type type_ofe_mixin.

  Global Instance ty_size_ne n : Proper (dist n ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_size_proper : Proper ((≡) ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_own_ne n:
    Proper (dist n ==> eq ==> eq ==> dist n) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_ne n :
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_proper :
    Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.

  Global Instance type_cofe : Cofe typeO.
  Proof.
    apply (iso_cofe_subtype' P type_pack type_unpack).
    - by intros [].
    - split; [by destruct 1|by intros [[??] ?]; constructor].
    - by intros [].
    - (* TODO: automate this *)
      repeat apply limit_preserving_and; repeat (apply limit_preserving_forall; intros ?).
      + apply bi.limit_preserving_Persistent=> n ty1 ty2 Hty; apply Hty.
      + apply bi.limit_preserving_entails=> n ty1 ty2 Hty. apply Hty. by rewrite Hty.
      + apply bi.limit_preserving_entails=> n ty1 ty2 Hty; repeat f_equiv; apply Hty.
      + apply bi.limit_preserving_entails=> n ty1 ty2 Hty; repeat f_equiv; apply Hty.
  Qed.

  Inductive st_equiv' (ty1 ty2 : simple_type) : Prop :=
    St_equiv :
      (∀ tid vs, ty1.(ty_own) tid vs ≡ ty2.(ty_own) tid vs) →
      st_equiv' ty1 ty2.
  Instance st_equiv : Equiv simple_type := st_equiv'.
  Inductive st_dist' (n : nat) (ty1 ty2 : simple_type) : Prop :=
    St_dist :
      (∀ tid vs, ty1.(ty_own) tid vs ≡{n}≡ (ty2.(ty_own) tid vs)) →
      st_dist' n ty1 ty2.
  Instance st_dist : Dist simple_type := st_dist'.

  Definition st_unpack (ty : simple_type) : thread_id -d> list val -d> iPropO Σ :=
    λ tid vl, ty.(ty_own) tid vl.

  Definition st_ofe_mixin : OfeMixin simple_type.
  Proof.
    apply (iso_ofe_mixin st_unpack).
    - split; [by destruct 1|by constructor].
    - split; [by destruct 1|by constructor].
  Qed.
  Canonical Structure stO : ofe := Ofe simple_type st_ofe_mixin.

  Global Instance st_own_ne n :
    Proper (dist n ==> eq ==> eq ==> dist n) st_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance st_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) st_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.

  Global Instance ty_of_st_ne : NonExpansive ty_of_st.
  Proof.
    intros n ?? EQ. constructor; try apply EQ. done.
    - simpl. intros; repeat f_equiv. apply EQ.
  Qed.
  Global Instance ty_of_st_proper : Proper ((≡) ==> (≡)) ty_of_st.
  Proof. apply (ne_proper _). Qed.
End ofe.

(** Special metric for type-nonexpansive and Type-contractive functions. *)
Section type_dist2.
  Context `{!typeG Σ}.

  (* Size and shr are n-equal, but own is only n-1-equal.
     We need this to express what shr has to satisfy on a Type-NE-function:
     It may only depend contractively on own. *)
  (* TODO: Find a better name for this metric. *)
  Inductive type_dist2 (n : nat) (ty1 ty2 : type) : Prop :=
    Type_dist2 :
      ty1.(ty_size) = ty2.(ty_size) →
      (∀ tid vs, dist_later n (ty1.(ty_own) tid vs) (ty2.(ty_own) tid vs)) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n}≡ ty2.(ty_shr) κ tid l) →
      type_dist2 n ty1 ty2.

  Global Instance type_dist2_equivalence n : Equivalence (type_dist2 n).
  Proof.
    constructor.
    - by constructor.
    - intros ?? Heq; constructor; symmetry; eapply Heq.
    - intros ??? Heq1 Heq2; constructor; etrans; (eapply Heq1 || eapply Heq2).
  Qed.

  Definition type_dist2_later (n : nat) ty1 ty2 : Prop :=
    match n with O => True | S n => type_dist2 n ty1 ty2 end.
  Arguments type_dist2_later !_ _ _ /.

  Global Instance type_dist2_later_equivalence n :
    Equivalence (type_dist2_later n).
  Proof. destruct n as [|n]. by split. apply type_dist2_equivalence. Qed.

  (* The hierarchy of metrics:
     dist n → type_dist2 n → dist_later n → type_dist2_later. *)
  Lemma type_dist_dist2 n ty1 ty2 : dist n ty1 ty2 → type_dist2 n ty1 ty2.
  Proof. intros EQ. split; intros; try apply dist_dist_later; apply EQ. Qed.
  Lemma type_dist2_dist_later n ty1 ty2 : type_dist2 n ty1 ty2 → dist_later n ty1 ty2.
  Proof.
    intros EQ. destruct n; first done. split; intros; try apply EQ.
    apply dist_S, EQ.
  Qed.
  Lemma type_later_dist2_later n ty1 ty2 : dist_later n ty1 ty2 → type_dist2_later n ty1 ty2.
  Proof. destruct n; first done. exact: type_dist_dist2. Qed.
  Lemma type_dist2_dist n ty1 ty2 : type_dist2 (S n) ty1 ty2 → dist n ty1 ty2.
  Proof. move=>/type_dist2_dist_later. done. Qed.
  Lemma type_dist2_S n ty1 ty2 : type_dist2 (S n) ty1 ty2 → type_dist2 n ty1 ty2.
  Proof. intros. apply type_dist_dist2, type_dist2_dist. done. Qed.

  Lemma ty_size_type_dist n : Proper (type_dist2 n ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Lemma ty_own_type_dist n:
    Proper (type_dist2 (S n) ==> eq ==> eq ==> dist n) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Lemma ty_shr_type_dist n :
    Proper (type_dist2 n ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
End type_dist2.

(** Type-nonexpansive and Type-contractive functions. *)
(* Note that TypeContractive is neither weaker nor stronger than Contractive, because
   (a) it allows the dependency of own on shr to be non-expansive, and
   (b) it forces the dependency of shr on own to be doubly-contractive.
   It would be possible to weaken this so that no double-contractivity is required.
   However, then it is no longer possible to write TypeContractive as just a
   Proper, which makes it significantly more annoying to use.
   For similar reasons, TypeNonExpansive is incomparable to NonExpansive.
*)
Notation TypeNonExpansive T := (∀ n, Proper (type_dist2 n ==> type_dist2 n) T).
Notation TypeContractive T := (∀ n, Proper (type_dist2_later n ==> type_dist2 n) T).

Section type_contractive.
  Context `{!typeG Σ}.

  Lemma type_ne_dist_later T :
    TypeNonExpansive T → ∀ n, Proper (type_dist2_later n ==> type_dist2_later n) T.
  Proof. intros Hf [|n]; last exact: Hf. hnf. by intros. Qed.

  (* From the above, it easily follows that TypeNonExpansive functions compose with
     TypeNonExpansive and with TypeContractive functions. *)
  Lemma type_ne_ne_compose T1 T2 :
    TypeNonExpansive T1 → TypeNonExpansive T2 → TypeNonExpansive (T1 ∘ T2).
  Proof. intros NE1 NE2 ? ???; simpl. apply: NE1. exact: NE2. Qed.

  Lemma type_contractive_compose_right T1 T2 :
    TypeContractive T1 → TypeNonExpansive T2 → TypeContractive (T1 ∘ T2).
  Proof. intros HT1 HT2 ? ???. apply: HT1. exact: type_ne_dist_later. Qed.

  Lemma type_contractive_compose_left T1 T2 :
    TypeNonExpansive T1 → TypeContractive T2 → TypeContractive (T1 ∘ T2).
  Proof. intros HT1 HT2 ? ???; simpl. apply: HT1. exact: HT2. Qed.

  (* Show some more relationships between properties. *)
  Lemma type_contractive_type_ne T :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    intros HT ? ???. apply type_dist_dist2, dist_later_dist, type_dist2_dist_later, HT. done.
  Qed.

  Lemma type_contractive_ne T :
    TypeContractive T → NonExpansive T.
  Proof.
    intros HT ? ???. apply dist_later_dist, type_dist2_dist_later, HT, type_dist_dist2. done.
  Qed.

  (* Simple types *)
  Global Instance ty_of_st_type_ne n :
    Proper (dist_later n ==> type_dist2 n) ty_of_st.
  Proof.
    intros ???. constructor.
    - done.
    - intros. destruct n; first done; simpl. f_equiv. done.
    - intros. solve_contractive.
  Qed.
End type_contractive.

(* Tactic automation. *)
Ltac f_type_equiv :=
  first [ ((eapply ty_size_type_dist || eapply ty_shr_type_dist || eapply ty_own_type_dist); try reflexivity) |
          match goal with | |- @dist_later ?A _ ?n ?x ?y =>
                            destruct n as [|n]; [exact I|change (@dist A _ n x y)]
          end ].
Ltac solve_type_proper :=
  constructor;
  solve_proper_core ltac:(fun _ => f_type_equiv || f_contractive || f_equiv).


Fixpoint shr_locsE (l : loc) (n : nat) : coPset :=
  match n with
  | 0%nat => ∅
  | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1%nat) n
  end.

Class Copy `{!typeG Σ} (t : type) := {
  copy_persistent tid vl : Persistent (t.(ty_own) tid vl);
  copy_shr_acc κ tid E F l q :
    ↑lftN ∪ ↑shrN ⊆ E → shr_locsE l (t.(ty_size) + 1) ⊆ F →
    lft_ctx -∗ t.(ty_shr) κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗
       ∃ q', na_own tid (F ∖ shr_locsE l t.(ty_size)) ∗
         ▷(l ↦∗{q'}: t.(ty_own) tid) ∗
      (na_own tid (F ∖ shr_locsE l t.(ty_size)) -∗ ▷l ↦∗{q'}: t.(ty_own) tid
                                  ={E}=∗ na_own tid F ∗ q.[κ])
}.
Existing Instances copy_persistent.
Instance: Params (@Copy) 2 := {}.

Class LstCopy `{!typeG Σ} (tys : list type) := lst_copy : Forall Copy tys.
Instance: Params (@LstCopy) 2 := {}.
Global Instance lst_copy_nil `{!typeG Σ} : LstCopy [] := List.Forall_nil _.
Global Instance lst_copy_cons `{!typeG Σ} ty tys :
  Copy ty → LstCopy tys → LstCopy (ty :: tys) := List.Forall_cons _ _ _.

Class Send `{!typeG Σ} (t : type) :=
  send_change_tid tid1 tid2 vl : t.(ty_own) tid1 vl -∗ t.(ty_own) tid2 vl.
Instance: Params (@Send) 2 := {}.

Class LstSend `{!typeG Σ} (tys : list type) := lst_send : Forall Send tys.
Instance: Params (@LstSend) 2 := {}.
Global Instance lst_send_nil `{!typeG Σ} : LstSend [] := List.Forall_nil _.
Global Instance lst_send_cons `{!typeG Σ} ty tys :
  Send ty → LstSend tys → LstSend (ty :: tys) := List.Forall_cons _ _ _.

Class Sync `{!typeG Σ} (t : type) :=
  sync_change_tid κ tid1 tid2 l : t.(ty_shr) κ tid1 l -∗ t.(ty_shr) κ tid2 l.
Instance: Params (@Sync) 2 := {}.

Class LstSync `{!typeG Σ} (tys : list type) := lst_sync : Forall Sync tys.
Instance: Params (@LstSync) 2 := {}.
Global Instance lst_sync_nil `{!typeG Σ} : LstSync [] := List.Forall_nil _.
Global Instance lst_sync_cons `{!typeG Σ} ty tys :
  Sync ty → LstSync tys → LstSync (ty :: tys) := List.Forall_cons _ _ _.

Section type.
  Context `{!typeG Σ}.

  (** Copy types *)
  Lemma shr_locsE_shift l n m :
    shr_locsE l (n + m) = shr_locsE l n ∪ shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n; intros l.
    - rewrite shift_loc_0. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /= IHn shift_loc_assoc.
      set_solver+.
  Qed.

  Lemma shr_locsE_disj l n m :
    shr_locsE l n ## shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n; intros l.
    - simpl. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /=.
      apply disjoint_union_l. split; last (rewrite -shift_loc_assoc; exact: IHn).
      clear IHn. revert n; induction m; intros n; simpl; first set_solver+.
      rewrite shift_loc_assoc. apply disjoint_union_r. split.
      + apply ndot_ne_disjoint. destruct l. intros [=]. lia.
      + rewrite -Z.add_assoc. move:(IHm (n + 1)%nat). rewrite Nat2Z.inj_add //.
  Qed.

  Lemma shr_locsE_shrN l n :
    shr_locsE l n ⊆ ↑shrN.
  Proof.
    revert l; induction n=>l /=; first by set_solver+.
    apply union_least; last by auto. solve_ndisj.
  Qed.

  Lemma shr_locsE_subseteq l n m :
    (n ≤ m)%nat → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    induction 1; first done. etrans; first done.
    rewrite -Nat.add_1_l [(_ + _)%nat]comm_L shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_split_tok l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢
      na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (l +ₗ n) m).
  Proof.
    rewrite shr_locsE_shift na_own_union //. apply shr_locsE_disj.
  Qed.

  Global Instance copy_equiv : Proper (equiv ==> impl) Copy.
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQown EQshr] Hty1. split.
    - intros. rewrite -EQown. apply _.
    - intros *. rewrite -EQsz -EQshr. setoid_rewrite <-EQown.
      apply copy_shr_acc.
  Qed.

  Global Program Instance ty_of_st_copy st : Copy (ty_of_st st).
  Next Obligation.
    iIntros (st κ tid E ? l q ? HF) "#LFT #Hshr Htok Hlft".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iDestruct "Hshr" as (vl) "[Hf Hown]".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first solve_ndisj.
    iModIntro. iExists _. iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iSplitL "Hmt1"; first by auto with iFrame.
    iIntros "Htok2 Hmt1". iDestruct "Hmt1" as (vl') "[Hmt1 #Hown']".
    iDestruct ("Htok" with "Htok2") as "$".
    iAssert (▷ ⌜length vl = length vl'⌝)%I as ">%".
    { iNext. iDestruct (st_size_eq with "Hown") as %->.
      iDestruct (st_size_eq with "Hown'") as %->. done. }
    iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op // Qp_div_2.
    iDestruct "Hmt" as "[>% Hmt]". subst. by iApply "Hclose".
  Qed.

  (** Send and Sync types *)
  Global Instance send_equiv : Proper (equiv ==> impl) Send.
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQown EQshr] Hty1.
    rewrite /Send=>???. rewrite -!EQown. auto.
  Qed.

  Global Instance sync_equiv : Proper (equiv ==> impl) Sync.
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQown EQshr] Hty1.
    rewrite /Send=>????. rewrite -!EQshr. auto.
  Qed.

  Global Instance ty_of_st_sync st : Send (ty_of_st st) → Sync (ty_of_st st).
  Proof.
    iIntros (Hsend κ tid1 tid2 l). iDestruct 1 as (vl) "[Hm Hown]".
    iExists vl. iFrame "Hm". iNext. by iApply Hsend.
  Qed.

  Lemma send_change_tid' t tid1 tid2 vl :
    Send t → t.(ty_own) tid1 vl ≡ t.(ty_own) tid2 vl.
  Proof.
    intros ?. apply: anti_symm; apply send_change_tid.
  Qed.

  Lemma sync_change_tid' t κ tid1 tid2 l :
    Sync t → t.(ty_shr) κ tid1 l ≡ t.(ty_shr) κ tid2 l.
  Proof.
    intros ?. apply: anti_symm; apply sync_change_tid.
  Qed.
End type.

Definition type_incl `{!typeG Σ} (ty1 ty2 : type) : iProp Σ :=
    (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
     (□ ∀ tid vl, ty1.(ty_own) tid vl -∗ ty2.(ty_own) tid vl) ∗
     (□ ∀ κ tid l, ty1.(ty_shr) κ tid l -∗ ty2.(ty_shr) κ tid l))%I.
Instance: Params (@type_incl) 2 := {}.
(* Typeclasses Opaque type_incl. *)

Definition type_equal `{!typeG Σ} (ty1 ty2 : type) : iProp Σ :=
    (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
     (□ ∀ tid vl, ty1.(ty_own) tid vl ∗-∗ ty2.(ty_own) tid vl) ∗
     (□ ∀ κ tid l, ty1.(ty_shr) κ tid l ∗-∗ ty2.(ty_shr) κ tid l))%I.
Instance: Params (@type_equal) 2 := {}.

Definition subtype `{!typeG Σ} (E : elctx) (L : llctx) (ty1 ty2 : type) : Prop :=
  ∀ qmax qL, llctx_interp_noend qmax L qL -∗ □ (elctx_interp E -∗ type_incl ty1 ty2).
Instance: Params (@subtype) 4 := {}.

(* TODO: The prelude should have a symmetric closure. *)
Definition eqtype `{!typeG Σ} (E : elctx) (L : llctx) (ty1 ty2 : type) : Prop :=
  subtype E L ty1 ty2 ∧ subtype E L ty2 ty1.
Instance: Params (@eqtype) 4 := {}.

Section subtyping.
  Context `{!typeG Σ}.

  Global Instance type_incl_ne : NonExpansive2 type_incl.
  Proof.
    intros n ?? [EQsz1%leibniz_equiv EQown1 EQshr1] ?? [EQsz2%leibniz_equiv EQown2 EQshr2].
    rewrite /type_incl. repeat ((by auto) || f_equiv).
  Qed.

  Global Instance type_incl_persistent ty1 ty2 : Persistent (type_incl ty1 ty2) := _.

  Lemma type_incl_refl ty : ⊢ type_incl ty ty.
  Proof. iSplit; first done. iSplit; iModIntro; iIntros; done. Qed.

  Lemma type_incl_trans ty1 ty2 ty3 :
    type_incl ty1 ty2 -∗ type_incl ty2 ty3 -∗ type_incl ty1 ty3.
  Proof.
    iIntros "(% & #Ho12 & #Hs12) (% & #Ho23 & #Hs23)".
    iSplit; first (iPureIntro; etrans; done).
    iSplit; iModIntro; iIntros.
    - iApply "Ho23". iApply "Ho12". done.
    - iApply "Hs23". iApply "Hs12". done.
  Qed.

  Lemma subtype_refl E L ty : subtype E L ty ty.
  Proof. iIntros (??) "_ !> _". iApply type_incl_refl. Qed.
  Global Instance subtype_preorder E L : PreOrder (subtype E L).
  Proof.
    split; first by intros ?; apply subtype_refl.
    iIntros (ty1 ty2 ty3 H12 H23 ??) "HL".
    iDestruct (H12 with "HL") as "#H12".
    iDestruct (H23 with "HL") as "#H23".
    iClear "∗". iIntros "!> #HE".
    iApply (type_incl_trans with "[#]"). by iApply "H12". by iApply "H23".
  Qed.

  Lemma subtype_Forall2_llctx_noend E L tys1 tys2 qmax qL :
    Forall2 (subtype E L) tys1 tys2 →
    llctx_interp_noend qmax L qL -∗ □ (elctx_interp E -∗
           [∗ list] tys ∈ (zip tys1 tys2), type_incl (tys.1) (tys.2)).
  Proof.
    iIntros (Htys) "HL".
    iAssert ([∗ list] tys ∈ zip tys1 tys2,
             □ (elctx_interp _ -∗ type_incl (tys.1) (tys.2)))%I as "#Htys".
    { iApply big_sepL_forall. iIntros (k [ty1 ty2] Hlookup).
      move:Htys => /Forall2_Forall /Forall_forall=>Htys.
      iApply (Htys (ty1, ty2)); first by exact: elem_of_list_lookup_2. done. }
    iClear "∗". iIntros "!> #HE". iApply (big_sepL_impl with "[$Htys]").
    iIntros "!> * % #Hincl". by iApply "Hincl".
  Qed.

  Lemma subtype_Forall2_llctx E L tys1 tys2 qmax :
    Forall2 (subtype E L) tys1 tys2 →
    llctx_interp qmax L -∗ □ (elctx_interp E -∗
           [∗ list] tys ∈ (zip tys1 tys2), type_incl (tys.1) (tys.2)).
  Proof.
    iIntros (?) "HL". iApply subtype_Forall2_llctx_noend; first done.
    iDestruct (llctx_interp_acc_noend with "HL") as "[$ _]".
  Qed.

  Lemma lft_invariant_subtype E L T :
    Proper (lctx_lft_eq E L ==> subtype E L) T.
  Proof.
    iIntros (x y [Hxy Hyx] qmax qL) "L".
    iPoseProof (Hxy with "L") as "#Hxy".
    iPoseProof (Hyx with "L") as "#Hyx".
    iIntros "!> #E". clear Hxy Hyx.
    iDestruct ("Hxy" with "E") as %Hxy.
    iDestruct ("Hyx" with "E") as %Hyx.
    iClear "Hyx Hxy".
    rewrite (anti_symm _ _ _ Hxy Hyx).
    iApply type_incl_refl.
  Qed.

  Lemma type_equal_incl ty1 ty2 :
    type_equal ty1 ty2 ⊣⊢ type_incl ty1 ty2 ∗ type_incl ty2 ty1.
  Proof.
    iSplit.
    - iIntros "#(% & Ho & Hs)".
      iSplit; (iSplit; first done; iSplit; iModIntro).
      + iIntros (??) "?". by iApply "Ho".
      + iIntros (???) "?". by iApply "Hs".
      + iIntros (??) "?". by iApply "Ho".
      + iIntros (???) "?". by iApply "Hs".
    - iIntros "#[(% & Ho1 & Hs1) (% & Ho2 & Hs2)]".
      iSplit; first done. iSplit; iModIntro.
      + iIntros (??). iSplit; [iApply "Ho1"|iApply "Ho2"].
      + iIntros (???). iSplit; [iApply "Hs1"|iApply "Hs2"].
  Qed.

  Lemma type_equal_refl ty :
    ⊢ type_equal ty ty.
  Proof.
    iApply type_equal_incl. iSplit; iApply type_incl_refl.
  Qed.
  Lemma type_equal_trans ty1 ty2 ty3 :
    type_equal ty1 ty2 -∗ type_equal ty2 ty3 -∗ type_equal ty1 ty3.
  Proof.
    rewrite !type_equal_incl. iIntros "#[??] #[??]". iSplit.
    - iApply (type_incl_trans _ ty2); done.
    - iApply (type_incl_trans _ ty2); done.
  Qed.

  Lemma lft_invariant_eqtype E L T :
    Proper (lctx_lft_eq E L ==> eqtype E L) T.
  Proof. split; by apply lft_invariant_subtype. Qed.

  Lemma equiv_subtype E L ty1 ty2 : ty1 ≡ ty2 → subtype E L ty1 ty2.
  Proof. unfold subtype, type_incl=>EQ. setoid_rewrite EQ. apply subtype_refl. Qed.

  Lemma eqtype_unfold E L ty1 ty2 :
    eqtype E L ty1 ty2 ↔
    (∀ qmax qL, llctx_interp_noend qmax L qL -∗ □ (elctx_interp E -∗ type_equal ty1 ty2)).
  Proof.
    split.
    - iIntros ([EQ1 EQ2] qmax qL) "HL".
      iDestruct (EQ1 with "HL") as "#EQ1".
      iDestruct (EQ2 with "HL") as "#EQ2".
      iClear "∗". iIntros "!> #HE".
      iDestruct ("EQ1" with "HE") as "[#Hsz [#H1own #H1shr]]".
      iDestruct ("EQ2" with "HE") as "[_ [#H2own #H2shr]]".
      iSplit; last iSplit.
      + done.
      + by iIntros "!>*"; iSplit; iIntros "H"; [iApply "H1own"|iApply "H2own"].
      + by iIntros "!>*"; iSplit; iIntros "H"; [iApply "H1shr"|iApply "H2shr"].
    - intros EQ. split; (iIntros (qmax qL) "HL";
      iDestruct (EQ with "HL") as "#EQ";
      iClear "∗"; iIntros "!> #HE";
      iDestruct ("EQ" with "HE") as "[% [#Hown #Hshr]]";
      (iSplit; last iSplit)).
      + done.
      + iIntros "!>* H". by iApply "Hown".
      + iIntros "!>* H". by iApply "Hshr".
      + done.
      + iIntros "!>* H". by iApply "Hown".
      + iIntros "!>* H". by iApply "Hshr".
  Qed.

  Lemma eqtype_refl E L ty : eqtype E L ty ty.
  Proof. by split. Qed.

  Lemma equiv_eqtype E L ty1 ty2 : ty1 ≡ ty2 → eqtype E L ty1 ty2.
  Proof. by split; apply equiv_subtype. Qed.

  Global Instance subtype_proper E L :
    Proper (eqtype E L ==> eqtype E L ==> iff) (subtype E L).
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance eqtype_equivalence E L : Equivalence (eqtype E L).
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma type_incl_simple_type (st1 st2 : simple_type) :
    □ (∀ tid vl, st1.(st_own) tid vl -∗ st2.(st_own) tid vl) -∗
    type_incl st1 st2.
  Proof.
    iIntros "#Hst". iSplit; first done. iSplit; iModIntro.
    - iIntros. iApply "Hst"; done.
    - iIntros (???). iDestruct 1 as (vl) "[Hf Hown]". iExists vl. iFrame "Hf".
      by iApply "Hst".
  Qed.

  Lemma subtype_simple_type E L (st1 st2 : simple_type) :
    (∀ qmax qL, llctx_interp_noend qmax L qL -∗ □ (elctx_interp E -∗
       ∀ tid vl, st1.(st_own) tid vl -∗ st2.(st_own) tid vl)) →
    subtype E L st1 st2.
  Proof.
    intros Hst. iIntros (qmax qL) "HL". iDestruct (Hst with "HL") as "#Hst".
    iClear "∗". iIntros "!> #HE". iApply type_incl_simple_type.
    iIntros "!>" (??) "?". by iApply "Hst".
  Qed.

  Lemma subtype_weaken E1 E2 L1 L2 ty1 ty2 :
    E1 ⊆+ E2 → L1 ⊆+ L2 →
    subtype E1 L1 ty1 ty2 → subtype E2 L2 ty1 ty2.
  Proof.
    iIntros (HE12 ? Hsub qmax qL) "HL". iDestruct (Hsub with "[HL]") as "#Hsub".
    { rewrite /llctx_interp. by iApply big_sepL_submseteq. }
    iClear "∗". iIntros "!> #HE". iApply "Hsub".
    rewrite /elctx_interp. by iApply big_sepL_submseteq.
  Qed.
End subtyping.

Section type_util.
  Context `{!typeG Σ}.

  Lemma heap_mapsto_ty_own l ty tid :
    l ↦∗: ty_own ty tid ⊣⊢ ∃ (vl : vec val ty.(ty_size)), l ↦∗ vl ∗ ty_own ty tid vl.
  Proof.
    iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]".
      iDestruct (ty_size_eq with "Hown") as %<-.
      iExists (list_to_vec vl). rewrite vec_to_list_to_vec. iFrame.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]". eauto with iFrame.
  Qed.

End type_util.

Global Hint Resolve ty_outlives_E_elctx_sat tyl_outlives_E_elctx_sat : lrust_typing.
Global Hint Resolve subtype_refl eqtype_refl : lrust_typing.
Global Hint Opaque subtype eqtype : lrust_typing.
