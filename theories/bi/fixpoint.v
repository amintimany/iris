From iris.bi Require Export bi.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Import bi.

(** Least and greatest fixpoint of a monotone function, defined entirely inside
    the logic.  *)
Class BIMonoPred {PROP : bi} {A : ofeT} (F : (A → PROP) → (A → PROP)) := {
  bi_mono_pred Φ Ψ : ((bi_persistently (∀ x, Φ x -∗ Ψ x)) → ∀ x, F Φ x -∗ F Ψ x)%I;
  bi_mono_pred_ne Φ : NonExpansive Φ → NonExpansive (F Φ)
}.
Arguments bi_mono_pred {_ _ _ _} _ _.
Local Existing Instance bi_mono_pred_ne.

Definition bi_least_fixpoint {PROP : bi} {A : ofeT}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  (∀ Φ : A -n> PROP, bi_persistently (∀ x, F Φ x -∗ Φ x) → Φ x)%I.

Definition bi_greatest_fixpoint {PROP : bi} {A : ofeT}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  (∃ Φ : A -n> PROP, bi_persistently (∀ x, Φ x -∗ F Φ x) ∧ Φ x)%I.

Section least.
  Context {PROP : bi} {A : ofeT} (F : (A → PROP) → (A → PROP)) `{!BIMonoPred F}.

  Global Instance least_fixpoint_ne : NonExpansive (bi_least_fixpoint F).
  Proof. solve_proper. Qed.

  Lemma least_fixpoint_unfold_2 x : F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x.
  Proof.
    iIntros "HF" (Φ) "#Hincl".
    iApply "Hincl". iApply (bi_mono_pred _ Φ with "[#]"); last done.
    iIntros "!#" (y) "Hy". iApply ("Hy" with "[# //]").
  Qed.

  Lemma least_fixpoint_unfold_1 x :
    bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x.
  Proof.
    iIntros "HF". iApply ("HF" $! (CofeMor (F (bi_least_fixpoint F))) with "[#]").
    iIntros "!#" (y) "Hy". iApply (bi_mono_pred with "[#]"); last done.
    iIntros "!#" (z) "?". by iApply least_fixpoint_unfold_2.
  Qed.

  Corollary least_fixpoint_unfold x :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using least_fixpoint_unfold_1, least_fixpoint_unfold_2.
  Qed.

  Lemma least_fixpoint_ind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F Φ y -∗ Φ y) -∗ ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof.
    iIntros "#HΦ" (x) "HF". by iApply ("HF" $! (CofeMor Φ) with "[#]").
  Qed.

  Lemma least_fixpoint_strong_ind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F (λ x, Φ x ∧ bi_least_fixpoint F x) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof.
    trans (∀ x, bi_least_fixpoint F x -∗ Φ x ∧ bi_least_fixpoint F x)%I.
    { iIntros "#HΦ". iApply (least_fixpoint_ind with "[]"); first solve_proper.
      iIntros "!#" (y) "H". iSplit; first by iApply "HΦ".
      iApply least_fixpoint_unfold_2. iApply (bi_mono_pred with "[#] H").
      by iIntros "!# * [_ ?]". }
    by setoid_rewrite and_elim_l.
  Qed.
End least.

Section greatest.
  Context {PROP : bi} {A : ofeT} (F : (A → PROP) → (A → PROP)) `{!BIMonoPred F}.

  Global Instance greatest_fixpoint_ne : NonExpansive (bi_greatest_fixpoint F).
  Proof. solve_proper. Qed.

  Lemma greatest_fixpoint_unfold_1 x :
    bi_greatest_fixpoint F x ⊢ F (bi_greatest_fixpoint F) x.
  Proof.
    iDestruct 1 as (Φ) "[#Hincl HΦ]".
    iApply (bi_mono_pred Φ (bi_greatest_fixpoint F) with "[#]").
    - iIntros "!#" (y) "Hy". iExists Φ. auto.
    - by iApply "Hincl".
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (bi_greatest_fixpoint F) x ⊢ bi_greatest_fixpoint F x.
  Proof.
    iIntros "HF". iExists (CofeMor (F (bi_greatest_fixpoint F))).
    iIntros "{$HF} !#" (y) "Hy". iApply (bi_mono_pred with "[#] Hy").
    iIntros "!#" (z) "?". by iApply greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    bi_greatest_fixpoint F x ≡ F (bi_greatest_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, Φ y -∗ F Φ y) -∗ ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
  Proof. iIntros "#HΦ" (x) "Hx". iExists (CofeMor Φ). auto. Qed.
End greatest.