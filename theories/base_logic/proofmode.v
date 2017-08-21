From iris.base_logic Require Export base_logic.
From iris.proofmode Require Export tactics.
From iris.base_logic Require Import proofmode_classes.
Import uPred.
Import bi.

Hint Extern 1 (coq_tactics.of_envs _ ⊢ |==> _) => iModIntro.

Section class_instances.
Context {M : ucmraT}.
Implicit Types P Q R : uPred M.

Global Instance from_assumption_bupd p P Q :
  FromAssumption p P Q → FromAssumption p P (|==> Q).
Proof. rewrite /FromAssumption=>->. apply bupd_intro. Qed.

Global Instance into_pure_cmra_valid `{CMRADiscrete A} (a : A) :
  @IntoPure (uPredI M) (✓ a) (✓ a).
Proof. by rewrite /IntoPure discrete_valid. Qed.

Global Instance from_pure_bupd P φ : FromPure P φ → FromPure (|==> P) φ.
Proof. rewrite /FromPure=> ->. apply bupd_intro. Qed.

Global Instance from_pure_cmra_valid {A : cmraT} (a : A) :
  @FromPure (uPredI M) (✓ a) (✓ a).
Proof.
  rewrite /FromPure. eapply bi.pure_elim; [done|]=> ?.
  rewrite -cmra_valid_intro //. by apply pure_intro.
Qed.

Global Instance into_wand_bupd p q R P Q :
  IntoWand false false R P Q → IntoWand p q (|==> R) (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !bare_always_if_elim HR.
  apply wand_intro_l. by rewrite bupd_sep wand_elim_r.
Qed.

Global Instance into_wand_bupd_persistent p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|==> R) P (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite bare_always_if_elim HR.
  apply wand_intro_l. by rewrite bupd_frame_l wand_elim_r.
Qed.

Global Instance into_wand_bupd_args p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite bare_always_if_elim bupd_wand_r.
Qed.

(* FromOp *)
(* TODO: Worst case there could be a lot of backtracking on these instances,
try to refactor. *)
Global Instance is_op_pair {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B) :
  IsOp a b1 b2 → IsOp a' b1' b2' → IsOp' (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance is_op_pair_persistent_l {A B : cmraT} (a : A) (a' b1' b2' : B) :
  Persistent a → IsOp a' b1' b2' → IsOp' (a,a') (a,b1') (a,b2').
Proof. constructor=> //=. by rewrite -persistent_dup. Qed.
Global Instance is_op_pair_persistent_r {A B : cmraT} (a b1 b2 : A) (a' : B) :
  Persistent a' → IsOp a b1 b2 → IsOp' (a,a') (b1,a') (b2,a').
Proof. constructor=> //=. by rewrite -persistent_dup. Qed.

Global Instance is_op_Some {A : cmraT} (a : A) b1 b2 :
  IsOp a b1 b2 → IsOp' (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.
(* This one has a higher precendence than [is_op_op] so we get a [+] instead of
an [⋅]. *)
Global Instance is_op_plus (n1 n2 : nat) : IsOp (n1 + n2) n1 n2.
Proof. done. Qed.

Global Instance from_sep_ownM (a b1 b2 : M) :
  IsOp a b1 b2 →
  FromSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /FromSep -ownM_op -is_op. Qed.
Global Instance from_sep_ownM_persistent (a b1 b2 : M) :
  IsOp a b1 b2 → Or (Persistent b1) (Persistent b2) →
  FromAnd (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros ? H. rewrite /FromAnd (is_op a) ownM_op.
  destruct H. by rewrite persistent_and_sep_l. by rewrite persistent_and_sep_r.
Qed.

Global Instance into_and_ownM p (a b1 b2 : M) :
  IsOp a b1 b2 → IntoAnd p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros. apply bare_always_if_mono. by rewrite (is_op a) ownM_op sep_and.
Qed.

Global Instance into_sep_ownM p (a b1 b2 : M) :
  IsOp a b1 b2 → IntoSep p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /IntoSep (is_op a) ownM_op. Qed.

Global Instance from_sep_bupd P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromSep=><-. apply bupd_sep. Qed.

Global Instance from_or_bupd P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof.
  rewrite /FromOr=><-.
  apply or_elim; apply bupd_mono; auto using or_intro_l, or_intro_r.
Qed.

Global Instance from_exist_bupd {A} P (Φ : A → uPred M) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

Global Instance from_modal_bupd P : FromModal (|==> P) P.
Proof. apply bupd_intro. Qed.

Global Instance elim_modal_bupd P Q : ElimModal (|==> P) P (|==> Q) (|==> Q).
Proof. by rewrite /ElimModal bupd_frame_r wand_elim_r bupd_trans. Qed.

Global Instance is_except_0_bupd P : IsExcept0 P → IsExcept0 (|==> P).
Proof.
  rewrite /IsExcept0=> HP.
  by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Qed.

Global Instance frame_bupd p R P Q : Frame p R P Q → Frame p R (|==> P) (|==> Q).
Proof. rewrite /Frame=><-. by rewrite bupd_frame_l. Qed.
End class_instances.
