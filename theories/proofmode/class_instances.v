From iris.proofmode Require Export classes.
From iris.bi Require Import bi tactics.
Set Default Proof Using "Type".
Import bi.

Section bi_instances.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(* IntoInternalEq *)
Global Instance into_internal_eq_internal_eq {A : ofeT} (x y : A) :
  @IntoInternalEq PROP A (x ≡ y) x y.
Proof. by rewrite /IntoInternalEq. Qed.
Global Instance into_internal_eq_always {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (□ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite always_elim_absorbing. Qed.
Global Instance into_internal_eq_bare {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (■ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite bare_elim. Qed.

(* FromBare *)
Global Instance from_bare_affine P : Affine P → FromBare P P.
Proof. intros. by rewrite /FromBare bare_elim. Qed.
Global Instance from_bare_default P : FromBare (■ P) P | 100.
Proof. by rewrite /FromBare. Qed.

(* FromAssumption *)
Global Instance from_assumption_exact p P : FromAssumption p P P | 0.
Proof. by rewrite /FromAssumption /= bare_always_if_elim. Qed.

Global Instance from_assumption_always_r P Q :
  FromAssumption true P Q → FromAssumption true P (□ Q).
Proof.
  rewrite /FromAssumption /= =><-.
  by rewrite -{1}bare_always_idemp bare_elim.
Qed.
Global Instance from_assumption_bare_r P Q :
  FromAssumption true P Q → FromAssumption true P (■ Q).
Proof. rewrite /FromAssumption /= =><-. by rewrite bare_idemp. Qed.

Global Instance from_assumption_bare_always_l p P Q :
  FromAssumption true P Q → FromAssumption p (⬕ P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite bare_always_if_elim. Qed.
Global Instance from_assumption_always_l_true P Q :
  FromAssumption true P Q → FromAssumption true (□ P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite always_idemp. Qed.
Global Instance from_assumption_always_l_false `{AffineBI PROP} P Q :
  FromAssumption true P Q → FromAssumption false (□ P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite affine_bare. Qed.

Global Instance from_assumption_forall {A} p (Φ : A → PROP) Q x :
  FromAssumption p (Φ x) Q → FromAssumption p (∀ x, Φ x) Q.
Proof. rewrite /FromAssumption=> <-. by rewrite forall_elim. Qed.

(* IntoPure *)
Global Instance into_pure_pure φ : @IntoPure PROP ⌜φ⌝ φ.
Proof. by rewrite /IntoPure. Qed.

Global Instance into_pure_eq {A : ofeT} (a b : A) :
  Timeless a → @IntoPure M (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure timeless_eq. Qed.

Global Instance into_pure_pure_and P1 P2 φ1 φ2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure pure_and. by intros -> ->. Qed.
Global Instance into_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /IntoPure pure_or. by intros -> ->. Qed.
Global Instance into_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl. by intros -> ->. Qed.

Global Instance into_pure_exist {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, IntoPure (Φ x) (φ x)) → IntoPure (∃ x, Φ x) (∃ x, φ x).
Proof. rewrite /IntoPure=>Hx. rewrite pure_exist. by setoid_rewrite Hx. Qed.
Global Instance into_pure_forall {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, IntoPure (Φ x) (φ x)) → IntoPure (∀ x, Φ x) (∀ x, φ x).
Proof. rewrite /IntoPure=>Hx. rewrite -pure_forall_2. by setoid_rewrite Hx. Qed.

Global Instance into_pure_pure_sep (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∗ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure=> -> ->. by rewrite sep_and pure_and. Qed.
Global Instance into_pure_pure_wand (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure=> <- ->. by rewrite pure_impl impl_wand_2.
Qed.

Global Instance into_pure_bare P φ : IntoPure P φ → IntoPure (■ P) φ.
Proof. rewrite /IntoPure=> ->. apply bare_elim. Qed.
Global Instance into_pure_always P φ : IntoPure P φ → IntoPure (□ P) φ.
Proof. rewrite /IntoPure=> ->. apply: always_elim_absorbing. Qed.

(* FromPure *)
Global Instance from_pure_pure φ : @FromPure PROP ⌜φ⌝ φ.
Proof. by rewrite /FromPure. Qed.
Global Instance from_pure_internal_eq {A : ofeT} (a b : A) :
  @FromPure PROP (a ≡ b) (a ≡ b).
Proof. by rewrite /FromPure pure_internal_eq. Qed.

Global Instance from_pure_pure_and (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure pure_and. by intros -> ->. Qed.
Global Instance from_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /FromPure pure_or. by intros -> ->. Qed.
Global Instance from_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl. by intros -> ->. Qed.

Global Instance from_pure_exist {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, FromPure (Φ x) (φ x)) → FromPure (∃ x, Φ x) (∃ x, φ x).
Proof. rewrite /FromPure=>Hx. rewrite pure_exist. by setoid_rewrite Hx. Qed.
Global Instance from_pure_forall {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, FromPure (Φ x) (φ x)) → FromPure (∀ x, Φ x) (∀ x, φ x).
Proof. rewrite /FromPure=>Hx. rewrite pure_forall. by setoid_rewrite Hx. Qed.

Global Instance from_pure_pure_sep (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∗ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure=> <- <-. by rewrite pure_and persistent_and_sep_l_1. Qed.
Global Instance from_pure_pure_wand (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure=> -> <-.
  by rewrite pure_wand_forall pure_impl pure_impl_forall.
Qed.

Global Instance from_pure_always P φ : FromPure P φ → FromPure (□ P) φ.
Proof. rewrite /FromPure=> <-. by rewrite always_pure. Qed.

(* IntoPersistentP *)
Global Instance into_persistentP_always_idemp P Q :
  IntoPersistentP P Q → IntoPersistentP (□ P) Q | 0.
Proof. rewrite /IntoPersistentP=> ->. by rewrite always_idemp. Qed.
Global Instance into_persistentP_always P : IntoPersistentP (□ P) P | 1.
Proof. by rewrite /IntoPersistentP. Qed.
Global Instance into_persistentP_persistent P :
  PersistentP P → IntoPersistentP P P | 100.
Proof. intros. by rewrite /IntoPersistentP (persistent_always P). Qed.
Global Instance into_persistentP_bare P Q :
  IntoPersistentP P Q → IntoPersistentP (■ P) Q | 0.
Proof. rewrite /IntoPersistentP=> ->. by rewrite bare_elim. Qed.

(* FromPersistentP *)
Global Instance from_persistentP_always P : FromPersistentP (□ P) P | 1.
Proof. by rewrite /FromPersistentP. Qed.
Global Instance from_persistentP_bare `{AffineBI PROP} P Q :
  FromPersistentP P Q → FromPersistentP (■ P) Q.
Proof. rewrite /FromPersistentP=> ->. by rewrite affine_bare. Qed.

(* IntoWand *)
Global Instance into_wand_wand p q P Q P' :
  FromAssumption q P P' → IntoWand p q (P' -∗ Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand=> HP. by rewrite HP bare_always_if_elim.
Qed.

Global Instance into_wand_impl_false_false `{!AffineBI PROP} P Q P' :
  FromAssumption false P P' → IntoWand false false (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => ->. apply wand_intro_r.
  by rewrite sep_and impl_elim_l.
Qed.

Global Instance into_wand_impl_false_true P Q P' :
  FromAssumption true P P' → Absorbing P' →
  IntoWand false true (P' → Q) P Q.
Proof.
  rewrite /IntoWand /FromAssumption /= => HP ?. apply wand_intro_l.
  rewrite -(bare_always_idemp P) HP.
  by rewrite -always_and_bare_sep_l always_elim_absorbing impl_elim_r.
Qed.

Global Instance into_wand_impl_true_false P Q P' :
  FromAssumption false P P' → Affine P' →
  IntoWand true false (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => HP ?. apply wand_intro_r.
  rewrite -always_and_bare_sep_l HP -{2}(affine_bare P') bare_and_l -bare_and_r.
  by rewrite bare_always_elim impl_elim_l.
Qed.

Global Instance into_wand_impl_true_true P Q P' :
  FromAssumption true P P' → IntoWand true true (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => <-. apply wand_intro_l.
  rewrite -{1}(bare_always_idemp P) -bare_always_sep -always_and_sep.
  by rewrite impl_elim_r bare_always_elim.
Qed.

Global Instance into_wand_and_l p q R1 R2 P' Q' :
  IntoWand p q R1 P' Q' → IntoWand p q (R1 ∧ R2) P' Q'.
Proof. rewrite /IntoWand=> ?. by rewrite /bi_wand_iff and_elim_l. Qed.
Global Instance into_wand_and_r p q R1 R2 P' Q' :
  IntoWand p q R2 Q' P' → IntoWand p q (R1 ∧ R2) Q' P'.
Proof. rewrite /IntoWand=> ?. by rewrite /bi_wand_iff and_elim_r. Qed.

Global Instance into_wand_forall {A} p q (Φ : A → PROP) P Q x :
  IntoWand p q (Φ x) P Q → IntoWand p q (∀ x, Φ x) P Q.
Proof. rewrite /IntoWand=> <-. by rewrite (forall_elim x). Qed.

Global Instance into_wand_always_true q R P Q :
  IntoWand true q R P Q → IntoWand true q (□ R) P Q.
Proof. by rewrite /IntoWand /= always_idemp. Qed.
Global Instance into_wand_always_false `{!AffineBI PROP} q R P Q :
  IntoWand false q R P Q → IntoWand false q (□ R) P Q.
Proof. by rewrite /IntoWand always_elim_absorbing. Qed.

Global Instance into_wand_bare_always p q R P Q :
  IntoWand p q R P Q → IntoWand p q (⬕ R) P Q.
Proof. by rewrite /IntoWand bare_always_elim. Qed.

(* FromAnd *)
Global Instance from_and_and P1 P2 : FromAnd (P1 ∧ P2) P1 P2 | 100.
Proof. by rewrite /FromAnd. Qed.
Global Instance from_and_sep_persistent_l P1 P1' P2 :
  FromBare P1 P1' → PersistentP P1' → FromAnd (P1 ∗ P2) P1' P2 | 9.
Proof.
  rewrite /FromBare /FromAnd=> <- ?. by rewrite persistent_and_bare_sep_l.
Qed.
Global Instance from_and_sep_persistent_r P1 P2 P2' :
  FromBare P2 P2' → PersistentP P2' → FromAnd (P1 ∗ P2) P1 P2' | 10.
Proof.
  rewrite /FromBare /FromAnd=> <- ?. by rewrite persistent_and_bare_sep_r.
Qed.
Global Instance from_and_sep_persistent P1 P2 :
  PersistentP P1 → PersistentP P2 → FromAnd (P1 ∗ P2) P1 P2 | 11.
Proof.
  rewrite /FromBare /FromAnd. intros ??. by rewrite -persistent_sep_and.
Qed.

Global Instance from_and_pure φ ψ : @FromAnd PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromAnd pure_and. Qed.

Global Instance from_and_bare P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite bare_and. Qed.
Global Instance from_and_always P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite always_and. Qed.
Global Instance from_and_always_sep P Q1 Q2 :
  FromSep P Q1 Q2 → FromAnd (□ P) (□ Q1) (□ Q2) | 11.
Proof. rewrite /FromAnd=> <-. by rewrite -always_and always_and_sep. Qed.

Hint Extern 10 => assumption : typeclass_instances. (* TODO: move *)

Global Instance from_and_big_sepL_cons_persistent {A} (Φ : nat → A → PROP) x l :
  PersistentP (Φ 0 x) →
  FromAnd ([∗ list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l, Φ (S k) y).
Proof. intros. by rewrite /FromAnd big_opL_cons persistent_and_sep_l_1. Qed.
Global Instance from_and_big_sepL_app_persistent {A} (Φ : nat → A → PROP) l1 l2 :
  (∀ k y, PersistentP (Φ k y)) →
  FromAnd ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof.
  intros. rewrite /FromAnd big_opL_app.
  destruct (decide (l1 = [])) as [->|]; simpl.
  - by rewrite left_id and_elim_r.
  - by rewrite persistent_and_sep_l_1.
Qed.

(* FromSep *)
Global Instance from_sep_sep P1 P2 : FromSep (P1 ∗ P2) P1 P2 | 100.
Proof. by rewrite /FromSep. Qed.
Global Instance from_sep_and P1 P2 :
  Or (Affine P1) (Absorbing P2) → Or (Affine P2) (Absorbing P1) →
  FromSep (P1 ∧ P2) P1 P2 | 101.
Proof. intros. by rewrite /FromSep sep_and. Qed.

Global Instance from_sep_pure φ ψ : @FromSep PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromSep pure_and sep_and. Qed.

Global Instance from_sep_bare P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromSep=> <-. by rewrite bare_sep. Qed.
Global Instance from_sep_always P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromSep=> <-. by rewrite always_sep. Qed.

Global Instance from_sep_big_sepL_cons {A} (Φ : nat → A → PROP) x l :
  FromSep ([∗ list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l, Φ (S k) y).
Proof. by rewrite /FromSep big_sepL_cons. Qed.
Global Instance from_sep_big_sepL_app {A} (Φ : nat → A → PROP) l1 l2 :
  FromSep ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. by rewrite /FromSep big_opL_app. Qed.

(* IntoAnd *)
Global Instance into_and_and p P Q : IntoAnd p (P ∧ Q) P Q.
Proof. by rewrite /IntoAnd bare_always_if_and. Qed.
Global Instance into_and_sep P Q : IntoAnd true (P ∗ Q) P Q.
Proof. by rewrite /IntoAnd /= bare_always_sep -bare_always_sep always_and_sep. Qed.

Global Instance into_and_pure p φ ψ : @IntoAnd PROP p ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoAnd pure_and bare_always_if_and. Qed.

Global Instance into_and_bare p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (■ P) (■ Q1) (■ Q2).
Proof.
  rewrite /IntoAnd. destruct p; simpl.
  - by rewrite -bare_and !always_bare.
  - intros ->. by rewrite bare_and.
Qed.
Global Instance into_and_always p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (□ P) (□ Q1) (□ Q2).
Proof.
  rewrite /IntoAnd /=. destruct p; simpl.
  - by rewrite -always_and !always_idemp.
  - intros ->. by rewrite always_and.
Qed.

(* IntoSep *)
Global Instance into_sep_sep p P Q : IntoSep p (P ∗ Q) P Q.
Proof. by rewrite /IntoSep bare_always_if_sep. Qed.
Global Instance into_sep_and P Q : IntoSep true (P ∧ Q) P Q.
Proof. by rewrite /IntoSep /= always_and_sep. Qed.

Global Instance into_sep_and_persistent_l P P' Q :
  PersistentP P → FromBare P' P → IntoSep false (P ∧ Q) P' Q.
Proof.
  rewrite /FromBare /IntoSep /=. intros ? <-.
  by rewrite persistent_and_bare_sep_l.
Qed.
Global Instance into_sep_and_persistent_r P Q Q' :
  PersistentP Q → FromBare Q' Q → IntoSep false (P ∧ Q) P Q'.
Proof.
  rewrite /FromBare /IntoSep /=. intros ? <-.
  by rewrite persistent_and_bare_sep_r.
Qed.

Global Instance into_sep_pure p φ ψ : @IntoSep PROP p ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof.
  by rewrite /IntoSep pure_and persistent_and_sep_l_1 bare_always_if_sep.
Qed.

Global Instance into_sep_bare p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (■ P) (■ Q1) (■ Q2).
Proof.
  rewrite /IntoSep /=. destruct p; simpl.
  - by rewrite -bare_sep !always_bare.
  - intros ->. by rewrite bare_sep.
Qed.
Global Instance into_sep_always p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (□ P) (□ Q1) (□ Q2).
Proof.
  rewrite /IntoSep /=. destruct p; simpl.
  - by rewrite -always_sep !always_idemp.
  - intros ->. by rewrite always_sep.
Qed.

(* We use [IsCons] and [IsApp] to make sure that [frame_big_sepL_cons] and
[frame_big_sepL_app] cannot be applied repeatedly often when having
[ [∗ list] k ↦ x ∈ ?e, Φ k x] with [?e] an evar. *)
Global Instance into_sep_big_sepL_cons {A} p (Φ : nat → A → PROP) l x l' :
  IsCons l x l' →
  IntoSep p ([∗ list] k ↦ y ∈ l, Φ k y)
    (Φ 0 x) ([∗ list] k ↦ y ∈ l', Φ (S k) y).
Proof. rewrite /IsCons=>->. by rewrite /IntoSep big_sepL_cons. Qed.
Global Instance into_sep_big_sepL_app {A} p (Φ : nat → A → PROP) l l1 l2 :
  IsApp l l1 l2 →
  IntoSep p ([∗ list] k ↦ y ∈ l, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. rewrite /IsApp=>->. by rewrite /IntoSep big_sepL_app. Qed.

(* FromOr *)
Global Instance from_or_or P1 P2 : FromOr (P1 ∨ P2) P1 P2.
Proof. by rewrite /FromOr. Qed.
Global Instance from_or_pure φ ψ : @FromOr PROP ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromOr pure_or. Qed.
Global Instance from_or_bare P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromOr=> <-. by rewrite bare_or. Qed.
Global Instance from_or_always P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromOr=> <-. by rewrite always_or. Qed.

(* IntoOr *)
Global Instance into_or_or P Q : IntoOr (P ∨ Q) P Q.
Proof. by rewrite /IntoOr. Qed.
Global Instance into_or_pure φ ψ : @IntoOr PROP ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoOr pure_or. Qed.
Global Instance into_or_bare P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (■ P) (■ Q1) (■ Q2).
Proof. rewrite /IntoOr=>->. by rewrite bare_or. Qed.
Global Instance into_or_always P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (□ P) (□ Q1) (□ Q2).
Proof. rewrite /IntoOr=>->. by rewrite always_or. Qed.

(* FromExist *)
Global Instance from_exist_exist {A} (Φ : A → PROP): FromExist (∃ a, Φ a) Φ.
Proof. by rewrite /FromExist. Qed.
Global Instance from_exist_pure {A} (φ : A → Prop) :
  @FromExist PROP A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /FromExist pure_exist. Qed.
Global Instance from_exist_bare {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite bare_exist. Qed.
Global Instance from_exist_always {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite always_exist. Qed.

(* IntoExist *)
Global Instance into_exist_exist {A} (Φ : A → PROP) : IntoExist (∃ a, Φ a) Φ.
Proof. by rewrite /IntoExist. Qed.
Global Instance into_exist_pure {A} (φ : A → Prop) :
  @IntoExist PROP A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /IntoExist pure_exist. Qed.
Global Instance into_exist_bare {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP bare_exist. Qed.
Global Instance into_exist_always {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP always_exist. Qed.

(* IntoForall *)
Global Instance into_forall_forall {A} (Φ : A → PROP) : IntoForall (∀ a, Φ a) Φ.
Proof. by rewrite /IntoForall. Qed.
Global Instance into_forall_bare {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP bare_forall. Qed.
Global Instance into_forall_always {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP always_forall. Qed.

(* ElimModal *)
Global Instance elim_modal_wand P P' Q Q' R :
  ElimModal P P' Q Q' → ElimModal P P' (R -∗ Q) (R -∗ Q').
Proof.
  rewrite /ElimModal=> H. apply wand_intro_r.
  by rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l.
Qed.
Global Instance forall_modal_wand {A} P P' (Φ Ψ : A → PROP) :
  (∀ x, ElimModal P P' (Φ x) (Ψ x)) → ElimModal P P' (∀ x, Φ x) (∀ x, Ψ x).
Proof.
  rewrite /ElimModal=> H. apply forall_intro=> a. by rewrite (forall_elim a).
Qed.

(* Frame *)
Global Instance frame_here_absorbing p R : Absorbing R → Frame p R R True.
Proof. intros. by rewrite /Frame bare_always_if_elim sep_elim_l. Qed.
Global Instance frame_here p R : Frame p R R emp.
Proof. intros. by rewrite /Frame bare_always_if_elim sep_elim_l. Qed.
Global Instance frame_here_pure p φ Q : FromPure Q φ → Frame p ⌜φ⌝ Q True.
Proof.
  rewrite /FromPure /Frame=> <-. by rewrite bare_always_if_elim sep_elim_l.
Qed.

Class MakeSep (P Q PQ : PROP) := make_sep : P ∗ Q ⊣⊢ PQ.
Arguments MakeSep _%I _%I _%I.
Global Instance make_sep_emp_l P : MakeSep emp P P.
Proof. by rewrite /MakeSep left_id. Qed.
Global Instance make_sep_emp_r P : MakeSep P emp P.
Proof. by rewrite /MakeSep right_id. Qed.
Global Instance make_sep_true_l P : Absorbing P → MakeSep True P P.
Proof. intros. by rewrite /MakeSep True_sep. Qed.
Global Instance make_sep_true_r P : Absorbing P → MakeSep P True P.
Proof. intros. by rewrite /MakeSep sep_True. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. by rewrite /MakeSep. Qed.

Global Instance frame_sep_persistent_l R P1 P2 Q1 Q2 Q' :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 → MakeSep Q1 Q2 Q' →
  Frame true R (P1 ∗ P2) Q' | 9.
Proof.
  rewrite /Frame /MaybeFrame /MakeSep /= => <- <- <-.
  rewrite {1}(always_sep_dup R) bare_sep. solve_sep_entails.
Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame false R P1 Q → MakeSep Q P2 Q' → Frame false R (P1 ∗ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r p R P1 P2 Q Q' :
  Frame p R P2 Q → MakeSep P1 Q Q' → Frame p R (P1 ∗ P2) Q' | 10.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc -(comm _ P1) assoc. Qed.

Global Instance frame_big_sepL_cons {A} p (Φ : nat → A → PROP) R Q l x l' :
  IsCons l x l' →
  Frame p R (Φ 0 x ∗ [∗ list] k ↦ y ∈ l', Φ (S k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsCons=>->. by rewrite /Frame big_sepL_cons. Qed.
Global Instance frame_big_sepL_app {A} p (Φ : nat → A → PROP) R Q l l1 l2 :
  IsApp l l1 l2 →
  Frame p R (([∗ list] k ↦ y ∈ l1, Φ k y) ∗
           [∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsApp=>->. by rewrite /Frame big_opL_app. Qed.

Class MakeAnd (P Q PQ : PROP) := make_and : P ∧ Q ⊣⊢ PQ.
Arguments MakeAnd _%I _%I _%I.
Global Instance make_and_true_l P : MakeAnd True P P.
Proof. by rewrite /MakeAnd left_id. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. by rewrite /MakeAnd right_id. Qed.
Global Instance make_and_emp_l P : Affine P → MakeAnd emp P P.
Proof. intros. by rewrite /MakeAnd emp_and. Qed.
Global Instance make_and_emp_r P : Affine P → MakeAnd P emp P.
Proof. intros. by rewrite /MakeAnd and_emp. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

Global Instance frame_and_l p R P1 P2 Q1 Q2 Q :
  Frame p R P1 Q1 → MaybeFrame p R P2 Q2 →
  MakeAnd Q1 Q2 Q → Frame p R (P1 ∧ P2) Q | 9.
Proof.
  rewrite /Frame /MakeAnd => <- <- <- /=.
  auto using and_intro, and_elim_l, and_elim_r, sep_mono.
Qed.
Global Instance frame_and_persistent_r R P1 P2 Q2 Q :
  Frame true R P2 Q2 →
  MakeAnd P1 Q2 Q → Frame true R (P1 ∧ P2) Q | 10.
Proof.
  rewrite /Frame /MakeAnd => <- <- /=. rewrite -!always_and_bare_sep_l.
  auto using and_intro, and_elim_l', and_elim_r'.
Qed.
Global Instance frame_and_r R P1 P2 Q2 Q :
  Or (Affine R) (Absorbing P1) →
  Frame false R P2 Q2 →
  MakeAnd P1 Q2 Q → Frame false R (P1 ∧ P2) Q | 10.
Proof.
  rewrite /Frame /MakeAnd=> ? <- <- /=. apply and_intro.
  - by rewrite and_elim_l sep_elim_r.
  - by rewrite and_elim_r.
Qed.

Class MakeOr (P Q PQ : PROP) := make_or : P ∨ Q ⊣⊢ PQ.
Arguments MakeOr _%I _%I _%I.
Global Instance make_or_true_l P : MakeOr True P True.
Proof. by rewrite /MakeOr left_absorb. Qed.
Global Instance make_or_true_r P : MakeOr P True True.
Proof. by rewrite /MakeOr right_absorb. Qed.
Global Instance make_or_emp_l P : Affine P → MakeOr emp P emp.
Proof. intros. by rewrite /MakeOr emp_or. Qed.
Global Instance make_or_emp_r P : Affine P → MakeOr P emp emp.
Proof. intros. by rewrite /MakeOr or_emp. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. by rewrite /MakeOr. Qed.

Global Instance frame_or_persistent_l R P1 P2 Q1 Q2 Q :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 → MakeOr Q1 Q2 Q →
  Frame true R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.
Global Instance frame_or_persistent_r R P1 P2 Q1 Q2 Q :
  MaybeFrame true R P2 Q2 → MakeOr P1 Q2 Q →
  Frame true R (P1 ∨ P2) Q | 10.
Proof.
  rewrite /Frame /MaybeFrame /MakeOr => <- <- /=.
  by rewrite sep_or_l sep_elim_r.
Qed.
Global Instance frame_or R P1 P2 Q1 Q2 Q :
  Frame false R P1 Q1 → Frame false R P2 Q2 → MakeOr Q1 Q2 Q →
  Frame false R (P1 ∨ P2) Q.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.

Global Instance frame_wand p R P1 P2 Q2 :
  Frame p R P2 Q2 → Frame p R (P1 -∗ P2) (P1 -∗ Q2).
Proof.
  rewrite /Frame=> ?. apply wand_intro_l.
  by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Qed.

Class MakeBare (P Q : PROP) := make_bare : ■ P ⊣⊢ Q.
Arguments MakeBare _%I _%I.
Global Instance make_bare_affine P : Affine P → MakeBare P P.
Proof. intros. by rewrite /MakeBare affine_bare. Qed.
Global Instance make_bare_default P : MakeBare P (■ P) | 100.
Proof. by rewrite /MakeBare. Qed.

Global Instance frame_bare R P Q Q' :
  Frame true R P Q → MakeBare Q Q' → Frame true R (■ P) Q'.
Proof. rewrite /Frame /MakeBare=> <- <- /=. by rewrite bare_sep bare_idemp. Qed.

Class MakeAlways (P Q : PROP) := make_always : □ P ⊣⊢ Q.
Arguments MakeAlways _%I _%I.
Global Instance make_always_true : MakeAlways True True.
Proof. by rewrite /MakeAlways always_pure. Qed.
Global Instance make_always_emp : MakeAlways emp True.
Proof. by rewrite /MakeAlways -always_True_emp always_pure. Qed.
Global Instance make_always_default P : MakeAlways P (□ P) | 100.
Proof. by rewrite /MakeAlways. Qed.

Global Instance frame_always R P Q Q' :
  Frame true R P Q → MakeAlways Q Q' → Frame true R (□ P) Q'.
Proof.
  rewrite /Frame /MakeAlways=> <- <- /=. rewrite -always_and_bare_sep_l.
  by rewrite always_sep always_bare always_idemp -always_and_sep_l_1.
Qed.

Global Instance frame_exist {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_forall {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.
End bi_instances.

Section sbi_instances.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

(* FromAssumption *)
Global Instance from_assumption_later p P Q :
  FromAssumption p P Q → FromAssumption p P (▷ Q)%I.
Proof. rewrite /FromAssumption=>->. apply later_intro. Qed.
Global Instance from_assumption_laterN n p P Q :
  FromAssumption p P Q → FromAssumption p P (▷^n Q)%I.
Proof. rewrite /FromAssumption=>->. apply laterN_intro. Qed.
Global Instance from_assumption_except_0 p P Q :
  FromAssumption p P Q → FromAssumption p P (◇ Q)%I.
Proof. rewrite /FromAssumption=>->. apply except_0_intro. Qed.

(* FromPure *)
Global Instance from_pure_later P φ : FromPure P φ → FromPure (▷ P) φ.
Proof. rewrite /FromPure=> ->. apply later_intro. Qed.
Global Instance from_pure_laterN n P φ : FromPure P φ → FromPure (▷^n P) φ.
Proof. rewrite /FromPure=> ->. apply laterN_intro. Qed.
Global Instance from_pure_except_0 P φ : FromPure P φ → FromPure (◇ P) φ.
Proof. rewrite /FromPure=> ->. apply except_0_intro. Qed.

(* IntoWand *)
Global Instance into_wand_later p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷ R) (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand /= => HR. by rewrite !bare_always_if_later -later_wand HR.
Qed.

Global Instance into_wand_later_args p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !bare_always_if_later (later_intro (⬕?p R)%I) -later_wand HR.
Qed.

Global Instance into_wand_laterN n p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷^n R) (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand /= => HR. by rewrite !bare_always_if_laterN -laterN_wand HR.
Qed.

Global Instance into_wand_laterN_args n p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !bare_always_if_laterN (laterN_intro _ (⬕?p R)%I) -laterN_wand HR.
Qed.

(* FromAnd *)
Global Instance from_and_later P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite later_and. Qed.
Global Instance from_and_laterN n P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromAnd=> <-. by rewrite laterN_and. Qed.
Global Instance from_and_except_0 P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromAnd=><-. by rewrite except_0_and. Qed.

(* FromSep *)
Global Instance from_sep_later P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromSep=> <-. by rewrite later_sep. Qed.
Global Instance from_sep_laterN n P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromSep=> <-. by rewrite laterN_sep. Qed.
Global Instance from_sep_except_0 P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromSep=><-. by rewrite except_0_sep. Qed.

(* IntoAnd *)
Global Instance into_and_later p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷ P) (▷ Q1) (▷ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply bare_always_if_intro'.
  by rewrite bare_always_if_later HP bare_always_if_elim later_and.
Qed.
Global Instance into_and_laterN n p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof.
  rewrite /IntoAnd=> HP. apply bare_always_if_intro'.
  by rewrite bare_always_if_laterN HP bare_always_if_elim laterN_and.
Qed.
Global Instance into_and_except_0 p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (◇ P) (◇ Q1) (◇ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply bare_always_if_intro'.
  by rewrite bare_always_if_except_0 HP bare_always_if_elim except_0_and.
Qed.

(* IntoSep *)
Global Instance into_sep_later p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (▷ P) (▷ Q1) (▷ Q2).
Proof.
  rewrite /IntoSep=> HP. apply bare_always_if_intro'.
  by rewrite bare_always_if_later HP bare_always_if_elim later_sep.
Qed.
Global Instance into_sep_laterN n p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof.
  rewrite /IntoSep=> HP. apply bare_always_if_intro'.
  by rewrite bare_always_if_laterN HP bare_always_if_elim laterN_sep.
Qed.
Global Instance into_sep_except_0 p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (◇ P) (◇ Q1) (◇ Q2).
Proof.
  rewrite /IntoSep=> HP. apply bare_always_if_intro'.
  by rewrite bare_always_if_except_0 HP bare_always_if_elim except_0_sep.
Qed.

(* FromOr *)
Global Instance from_or_later P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromOr=><-. by rewrite later_or. Qed.
Global Instance from_or_laterN n P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromOr=><-. by rewrite laterN_or. Qed.
Global Instance from_or_except_0 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromOr=><-. by rewrite except_0_or. Qed.

(* IntoOr *)
Global Instance into_or_later P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoOr=>->. by rewrite later_or. Qed.
Global Instance into_or_laterN n P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoOr=>->. by rewrite laterN_or. Qed.
Global Instance into_or_except_0 P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /IntoOr=>->. by rewrite except_0_or. Qed.

(* FromExist *)
Global Instance from_exist_later {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply later_mono, exist_intro.
Qed.
Global Instance from_exist_laterN {A} n P (Φ : A → PROP) :
  FromExist P Φ → FromExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply laterN_mono, exist_intro.
Qed.
Global Instance from_exist_except_0 {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite except_0_exist_2. Qed.

(* IntoExist *)
Global Instance into_exist_later {A} P (Φ : A → PROP) :
  IntoExist P Φ → Inhabited A → IntoExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP later_exist. Qed.
Global Instance into_exist_laterN {A} n P (Φ : A → PROP) :
  IntoExist P Φ → Inhabited A → IntoExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP laterN_exist. Qed.
Global Instance into_exist_except_0 {A} P (Φ : A → PROP) :
  IntoExist P Φ → Inhabited A → IntoExist (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP except_0_exist. Qed.

(* IsExcept0 *)
Global Instance is_except_0_except_0 P : IsExcept0 (◇ P).
Proof. by rewrite /IsExcept0 except_0_idemp. Qed.
Global Instance is_except_0_later P : IsExcept0 (▷ P).
Proof. by rewrite /IsExcept0 except_0_later. Qed.

(* FromModal *)
Global Instance from_modal_later P : FromModal (▷ P) P.
Proof. apply later_intro. Qed.
Global Instance from_modal_except_0 P : FromModal (◇ P) P.
Proof. apply except_0_intro. Qed.

(* ElimModal *)
Global Instance elim_modal_except_0 P Q : IsExcept0 Q → ElimModal (◇ P) P Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)%I).
  by rewrite -except_0_sep wand_elim_r.
Qed.
Global Instance elim_modal_timeless_later P Q :
  TimelessP P → IsExcept0 Q → ElimModal (▷ P) P Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)%I) (timelessP P).
  by rewrite -except_0_sep wand_elim_r.
Qed.
Global Instance elim_modal_timeless_later_if p P Q :
  TimelessP P → IsExcept0 Q → ElimModal (▷?p P) P Q Q.
Proof.
  destruct p; simpl; auto using elim_modal_timeless_later.
  intros _ _. by rewrite /ElimModal wand_elim_r.
Qed.

(* Frame *)
Class MakeLater (P lP : PROP) := make_later : ▷ P ⊣⊢ lP.
Arguments MakeLater _%I _%I.

Global Instance make_later_true : MakeLater True True.
Proof. by rewrite /MakeLater later_True. Qed.
Global Instance make_later_default P : MakeLater P (▷ P) | 100.
Proof. by rewrite /MakeLater. Qed.

Global Instance frame_later p R R' P Q Q' :
  IntoLaterN 1 R' R → Frame p R P Q → MakeLater Q Q' → Frame p R' (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLater /IntoLaterN=>-> <- <- /=.
  by rewrite bare_always_if_later later_sep.
Qed.

Class MakeLaterN (n : nat) (P lP : PROP) := make_laterN : ▷^n P ⊣⊢ lP.
Arguments MakeLaterN _%nat _%I _%I.

Global Instance make_laterN_true n : MakeLaterN n True True.
Proof. by rewrite /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_default P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

Global Instance frame_laterN p n R R' P Q Q' :
  IntoLaterN n R' R → Frame p R P Q → MakeLaterN n Q Q' → Frame p R' (▷^n P) Q'.
Proof.
  rewrite /Frame /MakeLaterN /IntoLaterN=>-> <- <-.
  by rewrite bare_always_if_laterN laterN_sep.
Qed.

Class MakeExcept0 (P Q : PROP) := make_except_0 : ◇ P ⊣⊢ Q.
Arguments MakeExcept0 _%I _%I.

Global Instance make_except_0_True : MakeExcept0 True True.
Proof. by rewrite /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. by rewrite /MakeExcept0. Qed.

Global Instance frame_except_0 p R P Q Q' :
  Frame p R P Q → MakeExcept0 Q Q' → Frame p R (◇ P) Q'.
Proof.
  rewrite /Frame /MakeExcept0=><- <-.
  by rewrite except_0_sep -(except_0_intro (⬕?p R)%I).
Qed.

(* IntoLater *)
Global Instance into_laterN_later n P Q :
  IntoLaterN n P Q → IntoLaterN' (S n) (▷ P) Q.
Proof. by rewrite /IntoLaterN' /IntoLaterN =>->. Qed.
Global Instance into_laterN_laterN n P : IntoLaterN' n (▷^n P) P.
Proof. by rewrite /IntoLaterN' /IntoLaterN. Qed.
Global Instance into_laterN_laterN_plus n m P Q :
  IntoLaterN m P Q → IntoLaterN' (n + m) (▷^n P) Q.
Proof. rewrite /IntoLaterN' /IntoLaterN=>->. by rewrite laterN_plus. Qed.

Global Instance into_laterN_and_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∧ P2) (Q1 ∧ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_and. Qed.
Global Instance into_laterN_and_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 → IntoLaterN' n (P ∧ P2) (P ∧ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_and -(laterN_intro _ P).
Qed.

Global Instance into_laterN_or_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∨ P2) (Q1 ∨ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_or. Qed.
Global Instance into_laterN_or_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 →
  IntoLaterN' n (P ∨ P2) (P ∨ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_or -(laterN_intro _ P).
Qed.

Global Instance into_laterN_sep_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∗ P2) (Q1 ∗ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_sep. Qed.
Global Instance into_laterN_sep_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 →
  IntoLaterN' n (P ∗ P2) (P ∗ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_sep -(laterN_intro _ P).
Qed.

Global Instance into_laterN_big_sepL n {A} (Φ Ψ : nat → A → PROP) (l: list A) :
  (∀ x k, IntoLaterN' n (Φ k x) (Ψ k x)) →
  IntoLaterN' n ([∗ list] k ↦ x ∈ l, Φ k x) ([∗ list] k ↦ x ∈ l, Ψ k x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opL_commute. by apply big_sepL_mono.
Qed.
Global Instance into_laterN_big_sepM n `{Countable K} {A}
    (Φ Ψ : K → A → PROP) (m : gmap K A) :
  (∀ x k, IntoLaterN' n (Φ k x) (Ψ k x)) →
  IntoLaterN' n ([∗ map] k ↦ x ∈ m, Φ k x) ([∗ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opM_commute. by apply big_sepM_mono.
Qed.
Global Instance into_laterN_big_sepS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gset A) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n ([∗ set] x ∈ X, Φ x) ([∗ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opS_commute. by apply big_sepS_mono.
Qed.
Global Instance into_laterN_big_sepMS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gmultiset A) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n ([∗ mset] x ∈ X, Φ x) ([∗ mset] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opMS_commute. by apply big_sepMS_mono.
Qed.

(* FromLater *)
Global Instance from_laterN_later P : FromLaterN 1 (▷ P) P | 0.
Proof. by rewrite /FromLaterN. Qed.
Global Instance from_laterN_laterN n P : FromLaterN n (▷^n P) P | 0.
Proof. by rewrite /FromLaterN. Qed.

(* The instances below are used when stripping a specific number of laters, or
to balance laters in different branches of ∧, ∨ and ∗. *)
Global Instance from_laterN_0 P : FromLaterN 0 P P | 100. (* fallthrough *)
Proof. by rewrite /FromLaterN. Qed.
Global Instance from_laterN_later_S n P Q :
  FromLaterN n P Q → FromLaterN (S n) (▷ P) Q.
Proof. by rewrite /FromLaterN=><-. Qed.
Global Instance from_laterN_later_plus n m P Q :
  FromLaterN m P Q → FromLaterN (n + m) (▷^n P) Q.
Proof. rewrite /FromLaterN=><-. by rewrite laterN_plus. Qed.

Global Instance from_later_and n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite laterN_and; apply and_mono. Qed.
Global Instance from_later_or n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite laterN_or; apply or_mono. Qed.
Global Instance from_later_sep n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∗ P2) (Q1 ∗ Q2).
Proof. intros ??; red. by rewrite laterN_sep; apply sep_mono. Qed.

Global Instance from_later_always n P Q :
  FromLaterN n P Q → FromLaterN n (□ P) (□ Q).
Proof. by rewrite /FromLaterN laterN_always=> ->. Qed.

Global Instance from_later_forall {A} n (Φ Ψ : A → PROP) :
  (∀ x, FromLaterN n (Φ x) (Ψ x)) → FromLaterN n (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /FromLaterN laterN_forall=> ?. by apply forall_mono. Qed.
Global Instance from_later_exist {A} n (Φ Ψ : A → PROP) :
  Inhabited A → (∀ x, FromLaterN n (Φ x) (Ψ x)) →
  FromLaterN n (∃ x, Φ x) (∃ x, Ψ x).
Proof. intros ?. rewrite /FromLaterN laterN_exist=> ?. by apply exist_mono. Qed.
End sbi_instances.
