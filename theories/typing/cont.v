From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Section typing.
  Context `{!typeG Σ}.

  (** Jumping to and defining a continuation. *)
  Lemma type_jump args argsv E L C T k T' :
    (* We use this rather complicated way to state that
         args = of_val <$> argsv, only because then solve_typing
         is able to prove it easily. *)
    Forall2 (λ a av, to_val a = Some av ∨ a = of_val av) args argsv →
    k ◁cont(L, T') ∈ C →
    tctx_incl E L T (T' (list_to_vec argsv)) →
    typed_body E L C T (k args).
  Proof.
    iIntros (Hargs HC Hincl tid) "#LFT #HE Hna HL HC HT".
    iMod (Hincl with "LFT HE HL HT") as "(HL & HT)".
    iSpecialize ("HC" with "[]"); first done.
    assert (args = of_val <$> argsv) as ->.
    { clear -Hargs. induction Hargs as [|a av ?? [<-%of_to_val| ->] _ ->]=>//=. }
    rewrite -{3}(vec_to_list_to_vec argsv). iApply ("HC" with "Hna HL HT").
  Qed.

  Lemma type_cont argsb L1 (T' : vec val (length argsb) → _) E L2 C T econt e2 kb :
    Closed (kb :b: argsb +b+ []) econt → Closed (kb :b: []) e2 →
    (∀ k, typed_body E L2 (k ◁cont(L1, T') :: C) T (subst' kb k e2)) -∗
    □ (∀ k (args : vec val (length argsb)),
          typed_body E L1 (k ◁cont(L1, T') :: C) (T' args)
                     (subst_v (kb::argsb) (k:::args) econt)) -∗
    typed_body E L2 C T (letcont: kb argsb := econt in e2).
  Proof.
    iIntros (Hc1 Hc2) "He2 #Hecont". iIntros (tid) "#LFT #HE Htl HL HC HT".
    rewrite (_ : (rec: kb argsb := econt)%E = of_val (rec: kb argsb := econt)%V); last by unlock.
    wp_let. iApply ("He2" with "LFT HE Htl HL [HC] HT").
    iLöb as "IH". iIntros (x) "H".
    iDestruct "H" as %[->|?]%elem_of_cons; last by iApply "HC".
    iIntros (args) "Htl HL HT". wp_rec.
    iApply ("Hecont" with "LFT HE Htl HL [HC] HT"). by iApply "IH".
  Qed.

  Lemma type_cont_norec argsb L1 (T' : vec val (length argsb) → _) E L2 C T econt e2 kb :
    Closed (kb :b: argsb +b+ []) econt → Closed (kb :b: []) e2 →
    (∀ k, typed_body E L2 (k ◁cont(L1, T') :: C) T (subst' kb k e2)) -∗
    (∀ k (args : vec val (length argsb)),
          typed_body E L1 C (T' args) (subst_v (kb :: argsb) (k:::args) econt)) -∗
    typed_body E L2 C T (letcont: kb argsb := econt in e2).
  Proof.
    iIntros (Hc1 Hc2) "He2 Hecont". iIntros (tid) "#LFT #HE Htl HL HC HT".
    rewrite (_ : (rec: kb argsb := econt)%E = of_val (rec: kb argsb := econt)%V); last by unlock.
    wp_let. iApply ("He2" with "LFT HE Htl HL [HC Hecont] HT").
    iIntros (x) "H".
    iDestruct "H" as %[->|?]%elem_of_cons; last by iApply "HC".
    iIntros (args) "Htl HL HT". wp_rec.
    iApply ("Hecont" with "LFT HE Htl HL HC HT").
  Qed.
End typing.
