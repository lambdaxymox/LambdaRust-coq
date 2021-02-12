From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section diverging_static.
  Context `{!typeG Σ}.

  (* Show that we can convert any live borrow to 'static with an infinite
     loop. *)
  Definition diverging_static_loop (call_once : val) : val :=
    funrec: <> ["x"; "f"] :=
      let: "call_once" := call_once in
      letcall: "ret" := "call_once" ["f"; "x"]%E in
    withcont: "loop":
      "loop" []
    cont: "loop" [] :=
      "loop" [].

  Lemma diverging_static_loop_type T F call_once
        `{!TyWf T, !TyWf F} :
    (* F : FnOnce(&'static T), as witnessed by the impl call_once *)
    typed_val call_once (fn(∅; F, &shr{static} T) → unit) →
    typed_val (diverging_static_loop call_once)
              (fn(∀ α, λ ϝ, ty_outlives_E T static; &shr{α} T, F) → ∅).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x f. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (call); simpl_subst.
    iApply (type_cont [_] [] (λ r, [(r!!!0%fin:val) ◁ box (unit)])).
    { iIntros (k). simpl_subst.
      iApply type_equivalize_lft_static.
      iApply (type_call [ϝ] ()); solve_typing. }
    iIntros "!# *". inv_vec args=>r. simpl_subst.
    iApply (type_cont [] [] (λ r, [])).
    { iIntros (kloop). simpl_subst. iApply type_jump; solve_typing. }
    iIntros "!# *". inv_vec args. simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (** Variant of the above where the lifetime is in an arbitrary invariant
      position.  This is incompatible with branding!

      Our [TyWf] is not working well for type constructors (we have no way of
      representing the fact that well-formedness is somewhat "uniform"), so we
      instead work with a constant [Euser] of lifetime inclusion assumptions (in
      general it could change with the type parameter but only in monotone ways)
      and a single [κuser] of lifetimes that have to be alive (making κuser a
      list would require some induction-based reasoning principles that we do
      not have, but showing that it works for one lifetime is enough to
      demonstrate the principle). *)
  Lemma diverging_static_loop_type' (T : lft → type) F κuser Euser call_once
        `{!TyWf F} :
    let _ : (∀ κ, TyWf (T κ)) := λ κ, {| ty_lfts := [κ; κuser]; ty_wf_E := Euser |} in
    (∀ κ1 κ2, (T κ1).(ty_size) = (T κ2).(ty_size)) →
    (∀ E L κ1 κ2, lctx_lft_eq E L κ1 κ2 → subtype E L (T κ1) (T κ2)) →
    typed_val call_once (fn(∅; F, T static) → unit) →
    typed_val (diverging_static_loop call_once)
              (fn(∀ α, ∅; T α, F) → ∅).
  Proof.
    intros HWf HTsz HTsub Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x f. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (call); simpl_subst.
    iApply (type_cont [_] [] (λ r, [(r!!!0%fin:val) ◁ box (unit)])).
    { iIntros (k). simpl_subst.
      iApply type_equivalize_lft_static.
      iApply (type_call [ϝ] ()); solve_typing. }
    iIntros "!# *". inv_vec args=>r. simpl_subst.
    iApply (type_cont [] [] (λ r, [])).
    { iIntros (kloop). simpl_subst. iApply type_jump; solve_typing. }
    iIntros "!# *". inv_vec args. simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

End diverging_static.
