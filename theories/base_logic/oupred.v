From iris.algebra Require Export ora.
From iris.bi Require Export derived_connectives.
From stdpp Require Import finite.
Set Default Proof Using "Type".
Local Hint Extern 1 (_ ≼ₒ _) => etrans; [eassumption|].
Local Hint Extern 1 (_ ≼ₒ _) => etrans; [|eassumption].
Local Hint Extern 10 (_ ≤ _) => omega.


(* TODO: change following text. *)

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(* A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the sProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *sProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in sProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   sProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

Record ouPred (M : uoraT) : Type := IProp {
  ouPred_holds :> nat → M → Prop;

  ouPred_mono n1 n2 x1 x2 :
    ouPred_holds n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → ouPred_holds n2 x2
}.
Arguments ouPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor ouPred.
Instance: Params (@ouPred_holds) 3.

Bind Scope bi_scope with ouPred.
Arguments ouPred_holds {_} _%I _ _.

Section cofe.
  Context {M : uoraT}.

  Inductive ouPred_equiv' (P Q : ouPred M) : Prop :=
    { ouPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance ouPred_equiv : Equiv (ouPred M) := ouPred_equiv'.
  Inductive ouPred_dist' (n : nat) (P Q : ouPred M) : Prop :=
    { ouPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance ouPred_dist : Dist (ouPred M) := ouPred_dist'.
  Definition ouPred_ofe_mixin : OfeMixin (ouPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure ouPredC : ofeT := OfeT (ouPred M) ouPred_ofe_mixin.

  Program Definition ouPred_compl : Compl ouPredC := λ c,
    {| ouPred_holds n x := ∀ n', n' ≤ n → ✓{n'}x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply ouPred_mono.
    eapply HP, ora_validN_orderN, ora_orderN_le=>//; lia.
    eapply ora_orderN_le=>//; lia. done.
  Qed.
  Global Program Instance uPred_cofe : Cofe ouPredC := {| compl := ouPred_compl |}.
  Next Obligation.
    intros n c; split=>i x Hin Hv.
    etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
    repeat intro. apply (chain_cauchy c n' i)=>//. by eapply ouPred_mono.
  Qed.
End cofe.
Arguments ouPredC : clear implicits.

Instance ouPred_ne {M} (P : ouPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply ouPred_mono; eauto; by rewrite Hx.
Qed.
Instance ouPred_proper {M} (P : ouPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply ouPred_ne, equiv_dist. Qed.

Lemma ouPred_holds_ne {M} (P Q : ouPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using ouPred_mono, ora_validN_le.
Qed.

(* TODO: remove!? *)
(* Equivalence to the definition of uPred in the appendix. *)
Lemma ouPred_alt {M : uoraT} (P: nat → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼ₒ{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼ₒ{n2} x2).
  { intros ????? H. eapply ora_orderN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using ora_orderN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition ouPred_map {M1 M2 : uoraT} (f : M2 -n> M1)
  `{!OraMorphism f} (P : ouPred M1) :
  ouPred M2 := {| ouPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using ouPred_mono, ora_morphism_monotoneN. Qed.

Instance ouPred_map_ne {M1 M2 : uoraT} (f : M2 -n> M1)
  `{!OraMorphism f} n : Proper (dist n ==> dist n) (ouPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using ora_morphism_validN.
Qed.
Lemma ouPred_map_id {M : uoraT} (P : ouPred M): ouPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma ouPred_map_compose {M1 M2 M3 : uoraT} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!OraMorphism f, !OraMorphism g} (P : ouPred M3):
  ouPred_map (g ◎ f) P ≡ ouPred_map f (ouPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma ouPred_map_ext {M1 M2 : uoraT} (f g : M1 -n> M2)
      `{!OraMorphism f} `{!OraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, ouPred_map f x ≡ ouPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /ouPred_holds /= Hf. Qed.
Definition ouPredC_map {M1 M2 : uoraT} (f : M2 -n> M1) `{!OraMorphism f} :
  ouPredC M1 -n> ouPredC M2 := CofeMor (ouPred_map f : ouPredC M1 → ouPredC M2).
Lemma ouPredC_map_ne {M1 M2 : uoraT} (f g : M2 -n> M1)
    `{!OraMorphism f, !OraMorphism g} n :
  f ≡{n}≡ g → ouPredC_map f ≡{n}≡ ouPredC_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /ouPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed.

Program Definition ouPredCF (F : uorarFunctor) : cFunctor := {|
  cFunctor_car A B := ouPredC (uorarFunctor_car F B A);
  cFunctor_map A1 A2 B1 B2 fg := ouPredC_map (uorarFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n P Q HPQ.
  apply ouPredC_map_ne, uorarFunctor_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A B P; simpl. rewrite -{2}(ouPred_map_id P).
  apply ouPred_map_ext=>y. by rewrite uorarFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' P; simpl. rewrite -ouPred_map_compose.
  apply ouPred_map_ext=>y; apply uorarFunctor_compose.
Qed.

Instance ouPredCF_contractive F :
  uorarFunctorContractive F → cFunctorContractive (ouPredCF F).
Proof.
  intros ? A1 A2 B1 B2 n P Q HPQ. apply ouPredC_map_ne, uorarFunctor_contractive.
  destruct n; split; by apply HPQ.
Qed.

(** logical entailement *)
Inductive ouPred_entails {M} (P Q : ouPred M) : Prop :=
  { ouPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Hint Resolve ouPred_mono : ouPred_def.

(** logical connectives *)
Program Definition ouPred_pure_def {M} (φ : Prop) : ouPred M :=
  {| ouPred_holds n x := φ |}.
Solve Obligations with done.
Definition ouPred_pure_aux : seal (@ouPred_pure_def). by eexists. Qed.
Definition ouPred_pure {M} := unseal ouPred_pure_aux M.
Definition ouPred_pure_eq :
  @ouPred_pure = @ouPred_pure_def := seal_eq ouPred_pure_aux.

Program Definition ouPred_emp {M} : ouPred M :=
{| ouPred_holds n x := ε ≼ₒ{n} x |}.
Next Obligation.
Proof.
  intros M n1 n2 x1 x2; simpl => Hx1 Hx2 Hn.
  eapply ora_orderN_le; last eassumption.
  etrans; eauto.
Qed.

Program Definition ouPred_and_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_and_aux : seal (@ouPred_and_def). by eexists. Qed.
Definition ouPred_and {M} := unseal ouPred_and_aux M.
Definition ouPred_and_eq: @ouPred_and = @ouPred_and_def := seal_eq ouPred_and_aux.

Program Definition ouPred_or_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_or_aux : seal (@ouPred_or_def). by eexists. Qed.
Definition ouPred_or {M} := unseal ouPred_or_aux M.
Definition ouPred_or_eq: @ouPred_or = @ouPred_or_def := seal_eq ouPred_or_aux.

Program Definition ouPred_impl_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ n' x',
       x ≼ₒ{n'} x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ Hle1 Hn1 n2 x3 Hle2 ?; simpl in *.
  apply HPQ; eauto.
  etrans; last apply Hle2.
  eapply ora_orderN_le; eauto.
Qed.
Definition ouPred_impl_aux : seal (@ouPred_impl_def). by eexists. Qed.
Definition ouPred_impl {M} := unseal ouPred_impl_aux M.
Definition ouPred_impl_eq :
  @ouPred_impl = @ouPred_impl_def := seal_eq ouPred_impl_aux.

Program Definition ouPred_forall_def {M A} (Ψ : A → ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_forall_aux : seal (@ouPred_forall_def). by eexists. Qed.
Definition ouPred_forall {M A} := unseal ouPred_forall_aux M A.
Definition ouPred_forall_eq :
  @ouPred_forall = @ouPred_forall_def := seal_eq ouPred_forall_aux.

Program Definition ouPred_exist_def {M A} (Ψ : A → ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_exist_aux : seal (@ouPred_exist_def). by eexists. Qed.
Definition ouPred_exist {M A} := unseal ouPred_exist_aux M A.
Definition ouPred_exist_eq: @ouPred_exist = @ouPred_exist_def := seal_eq ouPred_exist_aux.

Program Definition ouPred_internal_eq_def {M} {A : ofeT} (a1 a2 : A) : ouPred M :=
  {| ouPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=A)).
Definition ouPred_internal_eq_aux : seal (@ouPred_internal_eq_def). by eexists. Qed.
Definition ouPred_internal_eq {M A} := unseal ouPred_internal_eq_aux M A.
Definition ouPred_internal_eq_eq:
  @ouPred_internal_eq = @ouPred_internal_eq_def := seal_eq ouPred_internal_eq_aux.

Program Definition ouPred_sep_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∃ x1 x2, x1 ⋅ x2 ≼ₒ{n} x ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n1 n2 x y (x1&x2&Hx&?&?) ? ?.
  eexists x1, x2; repeat split; eauto using ouPred_mono.
  etrans; eapply ora_orderN_le; eauto.
Qed.
Definition ouPred_sep_aux : seal (@ouPred_sep_def). by eexists. Qed.
Definition ouPred_sep {M} := unseal ouPred_sep_aux M.
Definition ouPred_sep_eq: @ouPred_sep = @ouPred_sep_def := seal_eq ouPred_sep_aux.

Program Definition ouPred_wand_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply ouPred_mono with n3 (x1 ⋅ x3);
    eauto using ora_validN_orderN, ora_monoN_r, ora_orderN_le.
Qed.
Definition ouPred_wand_aux : seal (@ouPred_wand_def). by eexists. Qed.
Definition ouPred_wand {M} := unseal ouPred_wand_aux M.
Definition ouPred_wand_eq :
  @ouPred_wand = @ouPred_wand_def := seal_eq ouPred_wand_aux.

(* Equivalently, this could be `∀ y, P n y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
Program Definition ouPred_plainly_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using ouPred_mono, ucmra_unit_validN.
Definition ouPred_plainly_aux : seal (@ouPred_plainly_def). by eexists. Qed.
Definition ouPred_plainly {M} := unseal ouPred_plainly_aux M.
Definition ouPred_plainly_eq :
  @ouPred_plainly = @ouPred_plainly_def := seal_eq ouPred_plainly_aux.

Program Definition ouPred_persistently_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n (core x) |}.
Next Obligation.
  intros M P n1 n2 x1 x2 HP Hx Hn; simpl in *.
  eapply ouPred_mono; eauto. by apply ora_core_monoN.
Qed.
Definition ouPred_persistently_aux : seal (@ouPred_persistently_def). by eexists. Qed.
Definition ouPred_persistently {M} := unseal ouPred_persistently_aux M.
Definition ouPred_persistently_eq :
  @ouPred_persistently = @ouPred_persistently_def := seal_eq ouPred_persistently_aux.

Program Definition ouPred_later_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n1] [|n2] x1 x2; eauto using ouPred_mono, ora_orderN_S with lia.
Qed.
Definition ouPred_later_aux : seal (@ouPred_later_def). by eexists. Qed.
Definition ouPred_later {M} := unseal ouPred_later_aux M.
Definition ouPred_later_eq :
  @ouPred_later = @ouPred_later_def := seal_eq ouPred_later_aux.

Program Definition ouPred_ownM_def {M : uoraT} (a : M) : ouPred M :=
  {| ouPred_holds n x := a ≼ₒ{n} x |}.
Next Obligation.
  intros M a n1 n2 x1 x2; simpl => Hax1 Hx1x2 Hn.
  eapply ora_orderN_le; last eassumption.
  etrans; eauto.
Qed.
Definition ouPred_ownM_aux : seal (@ouPred_ownM_def). by eexists. Qed.
Definition ouPred_ownM {M} := unseal ouPred_ownM_aux M.
Definition ouPred_ownM_eq :
  @ouPred_ownM = @ouPred_ownM_def := seal_eq ouPred_ownM_aux.

Program Definition ouPred_ora_valid_def {M} {A : oraT} (a : A) : ouPred M :=
  {| ouPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using ora_validN_le.
Definition ouPred_ora_valid_aux : seal (@ouPred_ora_valid_def). by eexists. Qed.
Definition ouPred_ora_valid {M A} := unseal ouPred_ora_valid_aux M A.
Definition ouPred_ora_valid_eq :
  @ouPred_ora_valid = @ouPred_ora_valid_def := seal_eq ouPred_ora_valid_aux.

Module ouPred_unseal.
Definition unseal_eqs :=
  (ouPred_pure_eq, ouPred_and_eq, ouPred_or_eq, ouPred_impl_eq, ouPred_forall_eq,
  ouPred_exist_eq, ouPred_internal_eq_eq, ouPred_sep_eq, ouPred_wand_eq,
  ouPred_plainly_eq, ouPred_persistently_eq, ouPred_later_eq, ouPred_ownM_eq,
  ouPred_ora_valid_eq).
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl;
  unfold ouPred_emp, bi_pure, bi_and, bi_or, bi_impl, bi_forall, bi_exist,
  bi_sep, bi_wand, bi_plainly, bi_persistently, sbi_internal_eq, sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
  sbi_internal_eq, sbi_sep, sbi_wand, sbi_plainly, sbi_persistently; simpl;
  rewrite !unseal_eqs /=.
End ouPred_unseal.
Import ouPred_unseal.

Local Arguments ouPred_holds {_} !_ _ _ /.

Lemma ouPred_bi_mixin (M : uoraT) :
  BiMixin
    ouPred_entails ouPred_emp ouPred_pure ouPred_and ouPred_or ouPred_impl
    (@ouPred_forall M) (@ouPred_exist M) ouPred_sep ouPred_wand ouPred_plainly
    ouPred_persistently.
Proof.
  split.
  - (* PreOrder ouPred_entails *)
    split.
    + by intros P; split=> x i.
    + by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
  - (* (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P) *)
    intros P Q. split.
    + intros HPQ; split; split=> x i; apply HPQ.
    + intros [HPQ HQP]; split=> x n; by split; [apply HPQ|apply HQP].
  - (* Proper (iff ==> dist n) (@ouPred_pure M) *)
    intros φ1 φ2 Hφ. by unseal; split=> -[|n] ?; try apply Hφ.
  - (* NonExpansive2 ouPred_and *)
    intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  - (* NonExpansive2 ouPred_or *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  - (* NonExpansive2 ouPred_impl *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) ouPred_forall *)
    by intros A n Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) ouPred_exist *)
    intros A n Ψ1 Ψ2 HΨ.
    unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
  - (* NonExpansive2 ouPred_sep *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros (x1&x2&?&?&?); ofe_subst;
      exists x1, x2; split_and!; try (apply HP || apply HQ);
        eauto using ora_validN_op_l, ora_validN_orderN, ora_validN_op_r.
  - (* NonExpansive2 ouPred_wand *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros HPQ x' n'' ???;
      apply HQ, HPQ, HP; eauto using ora_validN_op_r.
  - (* NonExpansive ouPred_plainly *)
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP; eauto using @uora_unit_validN.
  - (* NonExpansive ouPred_persistently *)
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP;
      try apply @ora_core_validN; auto; try apply _.
  - (* φ → P ⊢ ⌜φ⌝ *)
    intros P φ ?. unseal; by split.
  - (* (φ → True ⊢ P) → ⌜φ⌝ ⊢ P *)
    intros φ P. unseal=> HP; split=> n x ??. by apply HP.
  - (* (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝ *)
    by unseal.
  - (* P ∧ Q ⊢ P *)
    intros P Q. unseal; by split=> n x ? [??].
  - (* P ∧ Q ⊢ Q *)
    intros P Q. unseal; by split=> n x ? [??].
  - (* (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R *)
    intros P Q R HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR].
  - (* P ⊢ P ∨ Q *)
    intros P Q. unseal; split=> n x ??; left; auto.
  - (* Q ⊢ P ∨ Q *)
    intros P Q. unseal; split=> n x ??; right; auto.
  - (* (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R *)
    intros P Q R HP HQ. unseal; split=> n x ? [?|?]. by apply HP. by apply HQ.
  - (* (P ∧ Q ⊢ R) → P ⊢ Q → R. *)
    intros P Q R. unseal => HQ; split=> n x ?? n' x' ????. apply HQ;
      naive_solver eauto using ouPred_mono, cmra_included_includedN.
  - (* (P ⊢ Q → R) → P ∧ Q ⊢ R *)
    intros P Q R. unseal=> HP; split=> n x ? [??]. apply HP with n x; auto.
  - (* (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a *)
    intros A P Ψ. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ.
  - (* (∀ a, Ψ a) ⊢ Ψ a *)
    intros A Ψ a. unseal; split=> n x ? HP; apply HP.
  - (* Ψ a ⊢ ∃ a, Ψ a *)
    intros A Ψ a. unseal; split=> n x ??; by exists a.
  - (* (∀ a, Ψ a ⊢ Q) → (∃ a, Ψ a) ⊢ Q *)
    intros A Ψ Q. unseal; intros HΨ; split=> n x ? [a ?]; by apply HΨ with a.
  - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
    intros P P' Q Q' HQ HQ'; unseal.
    split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x; repeat split;
      eauto 7 using ora_validN_op_l, ora_validN_op_r, ora_validN_orderN,
      ouPred_in_entails.
  - (* P ⊢ emp ∗ P *)
    intros P. rewrite /ouPred_emp. unseal; split=> n x ?? /=.
    exists (core x), x. rewrite ora_core_l; repeat split; auto.
    apply ora_order_orderN, uora_unit_order_core.
  - (* emp ∗ P ⊢ P *)
    intros P. unseal; split; intros n x ? (x1&x2&?&?&?); ofe_subst.
    eapply ouPred_mono; eauto.
    rewrite -(left_id _ _ x2). etrans; last eauto.
    by eapply ora_orderN_op.
  - (* P ∗ Q ⊢ Q ∗ P *)
    intros P Q. unseal; split; intros n x ? (x1&x2&?&?&?).
    exists x2, x1; by rewrite (comm op).
  - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
    intros P Q R. unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
    exists y1, (y2 ⋅ x2); split_and?; auto.
    + by rewrite (assoc op); setoid_rewrite <-Hx; setoid_rewrite Hy.
    + by exists y2, x2.
  - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
    intros P Q R. unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
    exists x, x'; split_and?; auto.
    eapply ouPred_mono; eauto using cmra_validN_op_l.
  - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
    intros P Q R. unseal=> HPQR. split; intros n x ? (?&?&?&HP&HQ).
    apply HPQR in HP; eauto using ora_validN_op_l, ora_validN_orderN.
    apply HP in HQ; eauto using ora_validN_orderN.
    eauto using ouPred_mono.
  - (* (P ⊢ Q) → bi_plainly P ⊢ bi_plainly Q *)
    intros P QR HP. unseal; split=> n x ? /=. by apply HP, uora_unit_validN.
  - (* bi_plainly P ⊢ bi_persistently P *)
    unseal; split; simpl => n x Hx HP.
    eapply ouPred_mono; eauto. apply ora_order_orderN, uora_unit_order_core.
  - (* bi_plainly P ⊢ bi_plainly (bi_plainly P) *)
    unseal; split=> n x ?? //.
  - (* (∀ a, bi_plainly (Ψ a)) ⊢ bi_plainly (∀ a, Ψ a) *)
    by unseal.
  - (* (bi_plainly P → bi_persistently Q) ⊢ bi_persistently (bi_plainly P → Q) *)
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply ouPred_mono with n' (core x)=>//.
    apply (HPQ n' x); eauto using ora_validN_le.
  - (* (bi_plainly P → bi_plainly Q) ⊢ bi_plainly (bi_plainly P → Q) *)
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply ouPred_mono with n' ε=>//.
    apply (HPQ n' x); eauto using ora_validN_le.
  - (* P ⊢ bi_plainly emp (ADMISSIBLE) *)
    by unseal; intros P; split => n x Hx HP /=.
  - (* bi_plainly P ∗ Q ⊢ bi_plainly P *)
    intros P Q. move: (ouPred_persistently P)=> P'.
    unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst;
      eauto using ouPred_mono, cmra_includedN_l.
  - (* (P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q *)
    intros P QR HP. unseal; split=> n x ? /=. by apply HP, ora_core_validN.
  - (* bi_persistently P ⊢ bi_persistently (bi_persistently P) *)
    intros P. unseal; split=> n x ?? /=. by rewrite ora_core_idemp.
  - (* bi_plainly (bi_persistently P) ⊢ bi_plainly P (ADMISSIBLE) *)
    intros P. unseal; split=> n  x ?? /=. by rewrite -(oracore_id_core ε).
  - (* (∀ a, bi_persistently (Ψ a)) ⊢ bi_persistently (∀ a, Ψ a) *)
    by unseal.
  - (* bi_persistently (∃ a, Ψ a) ⊢ ∃ a, bi_persistently (Ψ a) *)
    by unseal.
  - (* bi_persistently P ∗ Q ⊢ bi_persistently P (ADMISSIBLE) *)
    unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst.
    eapply ouPred_mono; eauto.
    etrans; last by apply ora_core_monoN; eassumption.
    eapply ora_order_orderN, uora_core_order_op.
  - (* bi_persistently P ∧ Q ⊢ (emp ∧ P) ∗ Q *)
    intros P Q. unseal; split=> n x ? [??]; simpl in *.
    exists (core x), x; rewrite ?ora_core_l; repeat split; auto.
    apply ora_order_orderN, uora_unit_order_core.
Qed.

Lemma ouPred_sbi_mixin (M : uoraT) : SbiMixin ouPred_ofe_mixin
  ouPred_entails ouPred_pure ouPred_and ouPred_or ouPred_impl
  (@ouPred_forall M) (@ouPred_exist M) ouPred_sep ouPred_plainly ouPred_persistently
  (@ouPred_internal_eq M) ouPred_later.
Proof.
  split.
  - (* Contractive sbi_later *)
    unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try omega.
    apply HPQ; eauto using ora_validN_S.
  - (* NonExpansive2 (@ouPred_internal_eq M A) *)
    intros A n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
    + by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
    + by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
  - (* P ⊢ a ≡ a *)
    intros A P a. unseal; by split=> n x ?? /=.
  - (* a ≡ b ⊢ Ψ a → Ψ b *)
    intros A a b Ψ Hnonexp.
    unseal; split=> n x ? Hab n' x' ??? HΨ. eapply Hnonexp with n a; auto.
  - (* (∀ x, f x ≡ g x) ⊢ f ≡ g *)
    by unseal.
  - (* `x ≡ `y ⊢ x ≡ y *)
    by unseal.
  - (* Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝ *)
    intros A a b ?. unseal; split=> n x ?; by apply (discrete_iff n).
  - (* bi_plainly ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q *)
    (* unseal; split=> n x ? /= HPQ; split=> n' x' ? HP; *)
    (* split; eapply HPQ; eauto using @ucmra_unit_least. *)
    admit.
  - (* Next x ≡ Next y ⊢ ▷ (x ≡ y) *)
    by unseal.
  - (* ▷ (x ≡ y) ⊢ Next x ≡ Next y *)
    by unseal.
  - (* (P ⊢ Q) → ▷ P ⊢ ▷ Q *)
    intros P Q.
    unseal=> HP; split=>-[|n] x ??; [done|apply HP; eauto using ora_validN_S].
  - (* (▷ P → P) ⊢ P *)
    intros P. unseal; split=> n x ? HP; induction n as [|n IH]; [by apply HP|].
    apply HP, IH, ouPred_mono with (S n) x; eauto using ora_validN_S.
  - (* (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a *)
    intros A Φ. unseal; by split=> -[|n] x.
  - (* (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a) *)
    intros A Φ. unseal; split=> -[|[|n]] x /=; eauto.
  - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *)
    intros P Q. unseal; split=> -[|n] x ? /=.
    { by exists x, (core x); rewrite ora_core_r. }
    intros (x1&x2&Hx&?&?); destruct (ora_extend n x x1 x2)
      as (y1&y2&Hx'&Hy1&Hy2); eauto using ora_validN_S; simpl in *.
    exists y1, y2; split; auto; by rewrite Hy1 Hy2.
  - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *)
    intros P Q. unseal; split=> -[|n] x ? /=; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2; eauto using ora_orderN_S.
  - (* ▷ bi_plainly P ⊢ bi_plainly (▷ P) *)
    by unseal.
  - (* bi_plainly (▷ P) ⊢ ▷ bi_plainly P *)
    by unseal.
  - (* ▷ bi_persistently P ⊢ bi_persistently (▷ P) *)
    by unseal.
  - (* bi_persistently (▷ P) ⊢ ▷ bi_persistently P *)
    by unseal.
  - (* ▷ P ⊢ ▷ False ∨ (▷ False → P) *)
    intros P. unseal; split=> -[|n] x ? /= HP; [by left|right].
    intros [|n'] x' ????; [|done].
    eapply ouPred_mono; [| eassumption | trivial].
    eapply ouPred_mono; eauto.
Admitted.

Canonical Structure ouPredI (M : uoraT) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (ouPred M); bi_bi_mixin := ouPred_bi_mixin M |}.
Canonical Structure ouPredSI (M : uoraT) : sbi :=
  {| sbi_ofe_mixin := ofe_mixin_of (ouPred M);
     sbi_bi_mixin := ouPred_bi_mixin M; sbi_sbi_mixin := ouPred_sbi_mixin M |}.

Coercion ouPred_valid {M} : ouPred M → Prop := bi_valid.

(* Latest notation *)
Notation "✓ x" := (ouPred_ora_valid x) (at level 20) : bi_scope.

Module ouPred.
Include ouPred_unseal.
Section ouPred.
Context {M : uoraT}.
Implicit Types φ : Prop.
Implicit Types P Q : ouPred M.
Implicit Types A : Type.
Arguments ouPred_holds {_} !_ _ _ /.
Hint Immediate ouPred_in_entails.

Global Instance ownM_ne : NonExpansive (@ouPred_ownM M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@ouPred_ownM M) := ne_proper _.

Global Instance cmra_valid_ne {A : oraT} :
  NonExpansive (@ouPred_ora_valid M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance cmra_valid_proper {A : oraT} :
  Proper ((≡) ==> (⊣⊢)) (@ouPred_ora_valid M A) := ne_proper _.

(** BI instances *)

(* Global Instance ouPred_affine : BiAffine (ouPredI M) | 0. *)
(* Proof. intros P. rewrite /Affine. by apply bi.pure_intro. Qed. *)

Global Instance ouPred_plainly_exist_1 : BiPlainlyExist (ouPredI M).
Proof. unfold BiPlainlyExist. by unseal. Qed.

(** Limits *)
Lemma entails_lim (cP cQ : chain (ouPredC M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply ouPred_holds_ne, Hlim, HP; eauto using conv_compl.
Qed.

(* Own *)
Lemma ownM_op (a1 a2 : M) :
  ouPred_ownM (a1 ⋅ a2) ⊣⊢ ouPred_ownM a1 ∗ ouPred_ownM a2.
Proof.
  rewrite /bi_sep /=; unseal. split=> n x ?; split; simpl; eauto.
  intros (x1&x2&Hx&Ha1&Ha2).
  setoid_rewrite <- Hx. etrans; first eapply ora_orderN_op; eauto.
  rewrite !(comm op x1); etrans; first eapply ora_orderN_op; eauto.
Qed.
Lemma persistently_ownM_core (a : M) :
  ouPred_ownM a ⊢ bi_persistently (ouPred_ownM (core a)).
Proof.
  rewrite /bi_persistently /=. unseal.
  split=> n x Hx /=. by apply ora_core_monoN.
Qed.
Lemma ownM_unit : bi_valid (ouPred_ownM (ε:M)).
Proof. unseal; split=> n x ? ?; done. Qed.
Lemma later_ownM (a : M) : ▷ ouPred_ownM a ⊢ ∃ b, ouPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  rewrite /bi_and /sbi_later /bi_exist /sbi_internal_eq /=; unseal.
  split=> -[|n] x /= ? Hax; first by eauto using ucmra_unit_leastN.
  destruct (ora_extend n x a ε) as (a'&y'&Hx&?&?); auto using ora_validN_S.
  { by rewrite right_id. }
  exists a'. split; auto. setoid_rewrite <- Hx. admit.
Admitted.

(* Valid *)
Lemma discrete_valid {A : oraT} `{!OraDiscrete A} (a : A) :
  ✓ a ⊣⊢ (⌜✓ a⌝ : ouPred M).
Proof. unseal. split=> n x _. by rewrite /= -ora_discrete_valid_iff. Qed.
Lemma ownM_valid (a : M) : ouPred_ownM a ⊢ ✓ a.
Proof.
  unseal; split=> n x Hv /= Hn; ofe_subst; eauto using ora_validN_orderN.
Qed.
Lemma ora_valid_intro {A : oraT} (a : A) :
  ✓ a → bi_valid (PROP:=ouPredI M) (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply ora_valid_validN. Qed.
Lemma ora_valid_elim {A : oraT} (a : A) : ¬ ✓{0} a → ✓ a ⊢ (False : ouPred M).
Proof.
  intros Ha. unseal. split=> n x ??; apply Ha, ora_validN_le with n; auto.
Qed.
Lemma plainly_cmra_valid_1 {A : oraT} (a : A) : ✓ a ⊢ bi_plainly (✓ a : ouPred M).
Proof. by unseal. Qed.
Lemma cmra_valid_weaken {A : oraT} (a b : A) : ✓ (a ⋅ b) ⊢ (✓ a : ouPred M).
Proof. unseal; split=> n x _; apply ora_validN_op_l. Qed.

(* Lemma prod_validI {A B : oraT} (x : A * B) : ✓ x ⊣⊢ (✓ x.1 ∧ ✓ x.2 : ouPred M). *)
(* Proof. by unseal. Qed. *)
(* Lemma option_validI {A : cmraT} (mx : option A) : *)
(*   ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : ouPred M end. *)
(* Proof. unseal. by destruct mx. Qed. *)

(* Lemma ofe_fun_validI `{Finite A} {B : A → uoraT} (g : ofe_fun B) : *)
(*   (✓ g : ouPred M) ⊣⊢ ∀ i, ✓ g i. *)
(* Proof. by ouPred.unseal. Qed. *)

(* Basic update modality *)
(* Global Instance bupd_facts : BUpdFacts (ouPredSI M). *)
(* Proof. *)
(*   split. *)
(*   - intros n P Q HPQ. *)
(*     unseal; split=> n' x; split; intros HP k yf ??; *)
(*     destruct (HP k yf) as (x'&?&?); auto; *)
(*     exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l. *)
(*   - unseal. split=> n x ? HP k yf ?; exists x; split; first done. *)
(*     apply ouPred_mono with n x; eauto using cmra_validN_op_l. *)
(*   - unseal. intros HPQ; split=> n x ? HP k yf ??. *)
(*     destruct (HP k yf) as (x'&?&?); eauto. *)
(*     exists x'; split; eauto using ouPred_in_entails, cmra_validN_op_l. *)
(*   - unseal; split; naive_solver. *)
(*   - unseal. split; intros n x ? (x1&x2&Hx&HP&?) k yf ??. *)
(*     destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto. *)
(*     { by rewrite assoc -(dist_le _ _ _ _ Hx); last lia. } *)
(*     exists (x' ⋅ x2); split; first by rewrite -assoc. *)
(*     exists x', x2. eauto using ouPred_mono, cmra_validN_op_l, cmra_validN_op_r. *)
(*   - unseal; split => n x Hnx /= Hng. *)
(*     destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto. *)
(*     eapply ouPred_mono; eauto using ucmra_unit_leastN. *)
(* Qed. *)

(* Lemma bupd_ownM_updateP x (Φ : M → Prop) : *)
(*   x ~~>: Φ → ouPred_ownM x ==∗ ∃ y, ⌜Φ y⌝ ∧ ouPred_ownM y. *)
(* Proof. *)
(*   intros Hup. unseal. split=> n x2 ? [x3 Hx] k yf ??. *)
(*   destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *. *)
(*   { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. } *)
(*   exists (y ⋅ x3); split; first by rewrite -assoc. *)
(*   exists y; eauto using cmra_includedN_l. *)
(* Qed. *)
End ouPred.
End ouPred.
