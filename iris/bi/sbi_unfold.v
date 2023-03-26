From iris.bi Require Export cmra internal_eq.
From iris.prelude Require Import options.
Local Set Default Proof Using "Type*".

(** The tactic takes a (bi-)entailment of plain propositions and turns it into a
a (bi-)implication in the pure step-indexed model. For example, given the goal:

  x ≼ y ⊣⊢ x.1 ≼ y.1 ∧ x.2 ≼ y.2

The tactic [sbi_unfold] turns it into

  ∀ n : nat, x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2

The tactic [sbi_unfold] works for goals of the shape [⊢ P], [P ⊢ Q], [P ⊣⊢ Q].
Here, [P] and [Q] should be in the "plain" subset of propositions, i.e., [⌜ _ ⌝],
[<si_pure>], [✓], [≡], [≼], closed under [∧], [∨], [→], [∀], [∃], [▷], and
[match]. The separating connectives [∗]/[-∗] are translated to [∧]/[→].

The tactic is implemented using the type class [SbiUnfold P Pi], which takes
a proposition [P] (which is intended to be plain) as input and produces its
interpretation [Pi : nat → Prop] in the step-indexed model as output. The
translation performed by the tactic intuitively involves two steps (a) translate
[P] into [<si_pure> φ], with [φ : siProp], and (b) unfold [φ] into a predicate
of type [nat → Prop]. The intermediate [siProp] is keps in the field
[sbi_unfold_car] of the class [SbiUnfold].

Note that this class lives in [Type] instead of [Prop]. To give instances for
[∀ x : A]/[∃ x : A] we to obtain the witness [sbi_unfold_car] for every [x]. *)
Class SbiUnfold `{!Sbi PROP} (P : PROP) (Pi : nat → Prop) := {
  sbi_unfold_car : siProp;
  sbi_unfold_as_si_pure : P ⊣⊢ <si_pure> sbi_unfold_car;
  sbi_unfold_siProp_holds n : siProp_holds sbi_unfold_car n ↔ Pi n;
}.
Global Hint Mode SbiUnfold + + ! - : typeclass_instances.
Global Arguments sbi_unfold_car {_ _} _ {_ _}.

Section sbi_unfold.
  Context `{Sbi PROP}.
  Implicit Types P Q : PROP.
  Local Arguments siProp_holds !_.
  Local Notation SbiUnfold := (SbiUnfold (PROP:=PROP)).

  (** The top-level lemmas used by the tactic *)
  Lemma sbi_unfold_entails `{!SbiUnfold P Pi, !SbiUnfold Q Qi} :
    (P ⊢ Q) ↔ ∀ n, Pi n → Qi n.
  Proof.
    rewrite [P]sbi_unfold_as_si_pure [Q]sbi_unfold_as_si_pure.
    rewrite si_pure_entails. split.
    - intros HPQ n. rewrite -(sbi_unfold_siProp_holds (P:=P)). intros.
      (* FIXME: if we remove the [intros] we trigger a Coq anomaly. *)
      rewrite -(sbi_unfold_siProp_holds (P:=Q)).
      by apply HPQ.
    - intros HPQ. split=> n. rewrite !sbi_unfold_siProp_holds. auto.
  Qed.

  Lemma sbi_unfold_equiv `{!SbiUnfold P Pi, !SbiUnfold Q Qi} :
    (∀ n, Pi n ↔ Qi n) → P ⊣⊢ Q.
  Proof. rewrite bi.equiv_entails !sbi_unfold_entails. naive_solver. Qed.

  Lemma sbi_unfold_emp_valid `{!SbiUnfold Q Qi} :
    (∀ n, Qi n) ↔ ⊢ Q.
  Proof.
    rewrite [Q]sbi_unfold_as_si_pure si_pure_emp_valid. split.
    - intros HQ. split=> n. rewrite !sbi_unfold_siProp_holds. auto.
    - intros HQ n. rewrite -(sbi_unfold_siProp_holds (P:=Q)). apply HQ.
      by siProp.unseal.
  Qed.

  (** The instances *)
  Global Instance sbi_unfold_pure φ : SbiUnfold ⌜ φ ⌝ (λ _, φ).
  Proof. exists ⌜ φ ⌝%I; [|by siProp.unseal]. by rewrite si_pure_pure. Qed.

  Global Instance sbi_unfold_internal_eq {A : ofe} (x y : A) :
    SbiUnfold (x ≡ y) (λ n, x ≡{n}≡ y).
  Proof. exists (x ≡ y)%I; [done |rewrite /internal_eq; by siProp.unseal]. Qed.

  Global Instance sbi_unfold_internal_cmra_valid {A : cmra} (x : A) :
    SbiUnfold (✓ x) (λ n, ✓{n} x).
  Proof. exists (✓ x)%I; [done|rewrite /internal_cmra_valid; by siProp.unseal]. Qed.

  Global Instance sbi_unfold_internal_included {A : cmra} (x y : A) :
    SbiUnfold (x ≼ y) (λ n, x ≼{n} y).
  Proof.
    exists (x ≼ y)%I.
    - by rewrite si_pure_internal_included.
    - rewrite /internal_included /internal_eq. by siProp.unseal.
  Qed.

  Global Instance sbi_unfold_si_pure Pi :
    SbiUnfold (<si_pure> Pi) (siProp_holds Pi).
  Proof. by exists Pi. Qed.

  Global Instance sbi_unfold_and P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P ∧ Q) (λ n, Pi n ∧ Qi n).
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii ∧ Qii)%I.
    - rewrite si_pure_and. by f_equiv.
    - siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_sep P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P ∗ Q) (λ n, Pi n ∧ Qi n).
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii ∧ Qii)%I.
    - rewrite si_pure_and_sep. by f_equiv.
    - siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_or P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P ∨ Q) (λ n, Pi n ∨ Qi n).
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii ∨ Qii)%I.
    - rewrite si_pure_or. by f_equiv.
    - siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_impl P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P → Q) (λ n, ∀ n', n' ≤ n → Pi n' → Qi n').
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii → Qii)%I.
    - rewrite si_pure_impl. by f_equiv.
    - siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_wand P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P -∗ Q) (λ n, ∀ n', n' ≤ n → Pi n' → Qi n').
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii → Qii)%I.
    - rewrite si_pure_impl_wand. by f_equiv.
    - siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_iff P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P ↔ Q) (λ n, ∀ n', n' ≤ n → Pi n' ↔ Qi n').
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii ↔ Qii)%I.
    - rewrite si_pure_iff. by f_equiv.
    - rewrite /bi_iff. siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_iff_wand P Q Pi Qi :
    SbiUnfold P Pi →
    SbiUnfold Q Qi →
    SbiUnfold (P ∗-∗ Q) (λ n, ∀ n', n' ≤ n → Pi n' ↔ Qi n').
  Proof.
    intros [Pii ??] [Qii ??]. exists (Pii ↔ Qii)%I.
    - rewrite si_pure_impl_iff_wand. by f_equiv.
    - rewrite /bi_iff. siProp.unseal. naive_solver.
  Qed.

  Global Instance sbi_unfold_forall {A} (Φ : A → PROP) Φi :
    (∀ x, SbiUnfold (Φ x) (Φi x)) →
    SbiUnfold (∀ x, Φ x) (λ n, ∀ x, Φi x n).
  Proof.
    intros HP. exists (∀ x, sbi_unfold_car (Φ x))%I.
    - rewrite si_pure_forall. f_equiv=> x. apply HP.
    - intros n. siProp.unseal. apply forall_proper=> x. apply HP.
  Qed.

  Global Instance sbi_unfold_exist {A} (Φ : A → PROP) Φi :
    (∀ x, SbiUnfold (Φ x)  (Φi x)) →
    SbiUnfold (∃ x, Φ x) (λ n, ∃ x, Φi x n).
  Proof.
    intros HP. exists (∃ x, sbi_unfold_car (Φ x))%I.
    - rewrite si_pure_exist. f_equiv=> x. apply HP.
    - intros n. siProp.unseal. f_equiv=> x. apply HP.
  Qed.

  Global Instance sbi_unfold_later P Pi :
    SbiUnfold P Pi →
    SbiUnfold (▷ P) (λ n, match n with 0 => True | S n' => Pi n' end).
  Proof.
    intros [Pii ??]. exists (▷ Pii)%I.
    - rewrite si_pure_later. by f_equiv.
    - siProp.unseal. by intros [].
  Qed.
End sbi_unfold.

(** We use a [Hint Extern] to translate [match]. Intuitively, we want an
instance:

  SbiUnfold (match x with Cj => Pj end) (λ n, match x with Cj => Pij n end)

Here, we have [SbiUnfold Pj Pij] for the branch of each constructor [Cj] in
the [match]. Actually generating [λ n, match x with Cj => Pij n end] is quite
fiddly. *)

(* A helper to help with HO-unification in the [Hint Extern] below. *)
Local Lemma sbi_unfold_tceq `{Sbi PROP} (P : PROP) Pi Pi' :
  SbiUnfold P Pi' → TCEq Pi Pi' → SbiUnfold P Pi.
Proof. by intros ? ->. Qed.

Global Hint Extern 0 (SbiUnfold (match ?x with _ => _ end) ?Pi) =>
  (* Use [unshelve] to turn the evar [Pi] into an explicit goal *)
  unshelve (let Pi' := open_constr:(_) in unify Pi Pi');
    [(* Refine [Pi] with [λ n, match x with .. => Pij n end], where each [Pij]
     is a new evar for constructor [j]. These evars are then shelved. *)
     intros ?; destruct x; shelve
    |(* Create an [SbiUnfold] goal for each constructor *)
     destruct x;
     (* These goals are of the form [SbiUnfold ?P (λ n, ?Pi_j)]. Since Coq's HO
     unification cannot handle the lambda reliably, we turn these goals into
     [SbiUnfold ?P ?Pi_j'] and generate equality goals [TCEq (λ n, ?Pi_j) ?Pi_j']
     that are solved later. *)
     class_apply sbi_unfold_tceq] :
  typeclass_instances.

Ltac sbi_unfold :=
  match goal with
  | |- ⊢ _ => apply sbi_unfold_emp_valid
  | |- _ ⊣⊢ _ => apply sbi_unfold_equiv
  | |- _ ⊢ _ => apply sbi_unfold_entails
  | |- _ => fail "sbi_unfold: not a BI entailment"
  end.
