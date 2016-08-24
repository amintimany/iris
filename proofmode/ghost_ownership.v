From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export ghost_ownership.

Section ghost.
Context `{inG Σ A}.
Implicit Types a b : A.

Global Instance into_and_own p γ a b1 b2 :
  IntoOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
Proof. intros. apply mk_into_and_sep. by rewrite (into_op a) own_op. Qed.
Global Instance from_sep_own γ a b :
  FromSep (own γ (a ⋅ b)) (own γ a) (own γ b) | 90.
Proof. by rewrite /FromSep own_op. Qed.
End ghost.
