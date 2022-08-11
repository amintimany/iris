(** IMPORTANT: Read the comment in [classes_make] about the "constant time"
requirements of these instances. *)
From iris.proofmode Require Export classes_make.
From iris.prelude Require Import options.
Import bi.

Section class_instances_make.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(** Affine *)
Global Instance bi_affine_quick_affine P : BiAffine PROP → QuickAffine P.
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance False_quick_affine : @QuickAffine PROP False.
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance emp_quick_affine : @QuickAffine PROP emp.
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance affinely_quick_affine P : QuickAffine (<affine> P).
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance intuitionistically_quick_affine P : QuickAffine (□ P).
Proof. rewrite /QuickAffine. apply _. Qed.

(** Absorbing *)
Global Instance bi_affine_quick_absorbing P : BiAffine PROP → QuickAbsorbing P.
Proof. rewrite /QuickAbsorbing. apply _. Qed.
Global Instance pure_quick_absorbing φ : @QuickAbsorbing PROP ⌜ φ ⌝.
Proof. rewrite /QuickAbsorbing. apply _. Qed.
Global Instance absorbingly_quick_absorbing P : QuickAbsorbing (<absorb> P).
Proof. rewrite /QuickAbsorbing. apply _. Qed.
Global Instance persistently_quick_absorbing P : QuickAbsorbing (<pers> P).
Proof. rewrite /QuickAbsorbing. apply _. Qed.

(** Embed *)
Global Instance make_embed_pure `{BiEmbed PROP PROP'} φ :
  KnownMakeEmbed (PROP:=PROP) ⌜φ⌝ ⌜φ⌝.
Proof. apply embed_pure. Qed.
Global Instance make_embed_emp `{BiEmbedEmp PROP PROP'} :
  KnownMakeEmbed (PROP:=PROP) emp emp.
Proof. apply embed_emp. Qed.
Global Instance make_embed_default `{BiEmbed PROP PROP'} P :
  MakeEmbed P ⎡P⎤ | 100.
Proof. by rewrite /MakeEmbed. Qed.

(** Sep *)
Global Instance make_sep_emp_l P : KnownLMakeSep emp P P.
Proof. apply left_id, _. Qed.
Global Instance make_sep_emp_r P : KnownRMakeSep P emp P.
Proof. apply right_id, _. Qed.
Global Instance make_sep_true_l P : QuickAbsorbing P → KnownLMakeSep True P P.
Proof. rewrite /QuickAbsorbing /KnownLMakeSep /MakeSep=> ?. by apply True_sep. Qed.
Global Instance make_sep_true_r P : QuickAbsorbing P →  KnownRMakeSep P True P.
Proof. rewrite /QuickAbsorbing /KnownLMakeSep /MakeSep=> ?. by apply sep_True. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. by rewrite /MakeSep. Qed.

(** And *)
Global Instance make_and_true_l P : KnownLMakeAnd True P P.
Proof. apply left_id, _. Qed.
Global Instance make_and_true_r P : KnownRMakeAnd P True P.
Proof. by rewrite /KnownRMakeAnd /MakeAnd right_id. Qed.
Global Instance make_and_emp_l P : QuickAffine P → KnownLMakeAnd emp P P.
Proof. apply emp_and. Qed.
Global Instance make_and_emp_r P : QuickAffine P → KnownRMakeAnd P emp P.
Proof. apply and_emp. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

(** Or *)
Global Instance make_or_true_l P : KnownLMakeOr True P True.
Proof. apply left_absorb, _. Qed.
Global Instance make_or_true_r P : KnownRMakeOr P True True.
Proof. by rewrite /KnownRMakeOr /MakeOr right_absorb. Qed.
Global Instance make_or_emp_l P : QuickAffine P → KnownLMakeOr emp P emp.
Proof. apply emp_or. Qed.
Global Instance make_or_emp_r P : QuickAffine P → KnownRMakeOr P emp emp.
Proof. apply or_emp. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. by rewrite /MakeOr. Qed.

(** Affinely *)
Global Instance make_affinely_True : @KnownMakeAffinely PROP True emp | 0.
-Proof. by rewrite /KnownMakeAffinely /MakeAffinely affinely_True_emp. Qed.
Global Instance make_affinely_affine P :
  QuickAffine P → MakeAffinely P P | 99.
Proof. apply affine_affinely. Qed.
Global Instance make_affinely_default P : MakeAffinely P (<affine> P) | 100.
Proof. by rewrite /MakeAffinely. Qed.

(** Absorbingly *)
Global Instance make_absorbingly_emp : @KnownMakeAbsorbingly PROP emp True | 0.
Proof.
  by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly -absorbingly_emp_True.
Qed.
Global Instance make_absorbingly_absorbing P :
  QuickAbsorbing P → MakeAbsorbingly P P | 99.
Proof. apply absorbing_absorbingly. Qed.
Global Instance make_absorbingly_default P : MakeAbsorbingly P (<absorb> P) | 100.
Proof. by rewrite /MakeAbsorbingly. Qed.

(** Intuitionistically *)
Global Instance make_intuitionistically_emp :
  @KnownMakeIntuitionistically PROP emp emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_emp.
Qed.
Global Instance make_intuitionistically_True :
  @KnownMakeIntuitionistically PROP True emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_True_emp.
Qed.
Global Instance make_intuitionistically_default P :
  MakeIntuitionistically P (□ P) | 100.
Proof. by rewrite /MakeIntuitionistically. Qed.

(** Later *)
Global Instance make_laterN_true n : @KnownMakeLaterN PROP n True True | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_emp `{!BiAffine PROP} n :
  @KnownMakeLaterN PROP n emp emp | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_emp. Qed.
Global Instance make_laterN_default n P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

(** Except-0 *)
Global Instance make_except_0_True : @KnownMakeExcept0 PROP True True.
Proof. by rewrite /KnownMakeExcept0 /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. by rewrite /MakeExcept0. Qed.
End class_instances_make.
