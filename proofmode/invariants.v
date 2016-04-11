From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export pviewshifts.
From iris.program_logic Require Export invariants.
Import uPred.

Section invariants.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.

Lemma tac_inv_fsa {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E N i P Q Φ :
  FSASplit Q E fsa fsaV Φ →
  fsaV → nclose N ⊆ E → of_envs Δ ⊢ inv N P →
  envs_app false (Esnoc Enil i (▷ P)) Δ = Some Δ' →
  Δ' ⊢ fsa (E ∖ nclose N) (λ a, ▷ P ★ Φ a) → Δ ⊢ Q.
Proof.
  intros ????? HΔ'. rewrite -(fsa_split Q). eapply (inv_fsa fsa); eauto.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.

Lemma tac_inv_fsa_timeless {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E N i P Q Φ :
  FSASplit Q E fsa fsaV Φ →
  fsaV → nclose N ⊆ E → of_envs Δ ⊢ inv N P → TimelessP P →
  envs_app false (Esnoc Enil i P) Δ = Some Δ' →
  Δ' ⊢ fsa (E ∖ nclose N) (λ a, P ★ Φ a) → Δ ⊢ Q.
Proof.
  intros ?????? HΔ'. rewrite -(fsa_split Q).
  eapply (inv_fsa_timeless fsa); eauto.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.
End invariants.

Tactic Notation "iInv" constr(N) "as" constr(pat) :=
  let H := iFresh in
  eapply tac_inv_fsa with _ _ _ _ N H _ _;
    [let P := match goal with |- FSASplit ?P _ _ _ _ => P end in
     apply _ || fail "iInv: cannot viewshift in goal" P
    |try fast_done (* atomic *)
    |done || eauto with ndisj (* [eauto with ndisj] is slow *)
    |iAssumption || fail "iInv: invariant" N "not found"
    |env_cbv; reflexivity
    |simpl (* get rid of FSAs *); iDestruct H as pat].

Tactic Notation "iInv>" constr(N) "as" constr(pat) :=
  let H := iFresh in
  eapply tac_inv_fsa_timeless with _ _ _ _ N H _ _;
    [let P := match goal with |- FSASplit ?P _ _ _ _ => P end in
     apply _ || fail "iInv: cannot viewshift in goal" P
    |try fast_done (* atomic *)
    |done || eauto with ndisj (* [eauto with ndisj] is slow *)
    |iAssumption || fail "iOpenInv: invariant" N "not found"
    |let P := match goal with |- TimelessP ?P => P end in
     apply _ || fail "iInv:" P "not timeless"
    |env_cbv; reflexivity
    |simpl (* get rid of FSAs *); iDestruct H as pat].
