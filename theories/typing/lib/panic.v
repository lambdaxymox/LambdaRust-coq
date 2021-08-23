From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

(* Minimal support for panic. Lambdarust does not support unwinding the
   stack. Instead, we just end the current thread by not calling any
   continuation.

   This properly models "panic=abort", but fails to take into account the
   trouble caused by unwinding. This is why we do not get into trouble with
   [take_mut]. *)

Section panic.
  Context `{!typeGS Σ}.

  Definition panic : val :=
    fn: [] := #☠.

  Lemma panic_type : typed_val panic (fn(∅) → ∅).
  Proof.
    intros E L. iApply type_fn; [done|]. iIntros "!> _ %κ %ret %args".
    inv_vec args. iIntros (tid qmax) "LFT HE Hna HL Hk HT /=". simpl_subst.
    by iApply wp_value.
  Qed.
End panic.
