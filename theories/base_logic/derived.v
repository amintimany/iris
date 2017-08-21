From iris.base_logic Require Export upred.
From iris.bi Require Export interface derived.
Set Default Proof Using "Type".
Import upred.uPred.
Import interface.bi derived.bi.

Module uPred.
Section derived.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

(* Limits *)
Lemma limit_preserving_entails {A : ofeT} `{Cofe A} (Φ Ψ : A → uPred M) :
  NonExpansive Φ → NonExpansive Ψ → LimitPreserving (λ x, Φ x ⊢ Ψ x).
Proof.
  intros HΦ HΨ c Hc. etrans; [apply equiv_spec, compl_chain_map|].
  etrans; [|apply equiv_spec, symmetry, compl_chain_map].
  by apply entails_lim.
Qed.
Lemma limit_preserving_equiv {A : ofeT} `{Cofe A} (Φ Ψ : A → uPred M) :
  NonExpansive Φ → NonExpansive Ψ → LimitPreserving (λ x, Φ x ⊣⊢ Ψ x).
Proof.
  intros HΦ HΨ. eapply limit_preserving_ext.
  { intros x. symmetry; apply equiv_spec. }
  apply limit_preserving_and; by apply limit_preserving_entails.
Qed.

(* Affine *)
Global Instance uPred_affine : AffineBI (uPredI M) | 0.
Proof. intros P. rewrite /Affine. by apply bi.pure_intro. Qed.

(* Own and valid derived *)
Lemma always_ownM (a : M) : Persistent a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
Proof.
  intros; apply (anti_symm _); first by apply: always_elim_absorbing.
  by rewrite {1}always_ownM_core persistent_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → uPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid cmra_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM M).
Proof. intros a b [b' ->]. by rewrite ownM_op sep_elim_l. Qed.
Lemma ownM_empty' : uPred_ownM ∅ ⊣⊢ True.
Proof. apply (anti_symm _); first by apply pure_intro. apply ownM_empty. Qed.
Lemma always_cmra_valid {A : cmraT} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  intros; apply (anti_symm _); first by apply: always_elim_absorbing.
  apply:always_cmra_valid_1.
Qed.

(** * Derived rules *)
Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) (@uPred_bupd M).
Proof. intros P Q; apply bupd_mono. Qed.
Global Instance bupd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) (@uPred_bupd M).
Proof. intros P Q; apply bupd_mono. Qed.
Lemma bupd_frame_l R Q : (R ∗ |==> Q) ==∗ R ∗ Q.
Proof. rewrite !(comm _ R); apply bupd_frame_r. Qed.
Lemma bupd_wand_l P Q : (P -∗ Q) ∗ (|==> P) ==∗ Q.
Proof. by rewrite bupd_frame_l wand_elim_l. Qed.
Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ==∗ Q.
Proof. by rewrite bupd_frame_r wand_elim_r. Qed.
Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ==∗ P ∗ Q.
Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.
Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
Proof.
  rewrite /bi_except_0. apply or_elim; auto using bupd_mono, or_intro_r.
  by rewrite -bupd_intro -or_intro_l.
Qed.

(* Timeless instances *)
Global Instance valid_timeless {A : cmraT} `{CMRADiscrete A} (a : A) :
  TimelessP (✓ a : uPred M)%I.
Proof. rewrite /TimelessP !discrete_valid. apply (timelessP _). Qed.
Global Instance ownM_timeless (a : M) : Timeless a → TimelessP (uPred_ownM a).
Proof.
  intros ?. rewrite /TimelessP later_ownM. apply exist_elim=> b.
  rewrite (timelessP (a≡b)) (except_0_intro (uPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (uPred_ownM) _);
    auto using and_elim_l, and_elim_r.
Qed.

(* Derived lemmas for persistence *)
Global Instance limit_preserving_PersistentP {A:ofeT} `{Cofe A} (Φ : A → uPred M) :
  NonExpansive Φ → LimitPreserving (λ x, PersistentP (Φ x)).
Proof. intros. apply limit_preserving_equiv; solve_proper. Qed.

(* Persistence *)
Global Instance cmra_valid_persistent {A : cmraT} (a : A) :
  PersistentP (✓ a : uPred M)%I.
Proof. by intros; rewrite /PersistentP always_cmra_valid. Qed.
Global Instance ownM_persistent : Persistent a → PersistentP (@uPred_ownM M a).
Proof. intros. by rewrite /PersistentP always_ownM. Qed.

(* For big ops *)
Global Instance uPred_ownM_sep_homomorphism :
  MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM M).
Proof. split; [split; try apply _|]. apply ownM_op. apply ownM_empty'. Qed.
End derived.

(* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [AffineBI] as a premise. *)
Hint Immediate uPred_affine.
End uPred.
