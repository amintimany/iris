From iris.algebra Require Export ofe monoid cmra.
From stdpp Require Import finite.
Set Default Proof Using "Type".

Hint Extern 10 => eassumption : typeclass_instances.

(* The order of an ordered RA quantifies over [A], not [option A].  This means
   we do not get reflexivity.  However, if we used [option A], the following
   would no longer hold:
     x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2
*)
Class OraOrder A := Oraorder : A → A → Prop.
Infix "≼ₒ" := Oraorder (at level 70) : stdpp_scope.
Notation "(≼ₒ)" := Oraorder (only parsing) : stdpp_scope.
Hint Extern 0 (_ ≼ₒ _) => reflexivity.
Instance: Params (@Oraorder) 2.

Class OraOrderN A := OraorderN : nat → A → A → Prop.
Notation "x ≼ₒ{ n } y" := (OraorderN n x y)
  (at level 70, n at next level, format "x  ≼ₒ{ n }  y") : stdpp_scope.
Notation "(≼ₒ{ n })" := (OraorderN n) (only parsing) : stdpp_scope.
Instance: Params (@OraorderN) 3.
Hint Extern 0 (_ ≼ₒ{_} _) => reflexivity.

Class Increasing `{Op A, OraOrder A} (x : A) := increasing : ∀ y, y ≼ₒ x ⋅ y.
Arguments increasing {_ _ _} _ {_}.

Section mixin.
  Local Set Primitive Projections.
  Record OraMixin A `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A,
                      OraOrder A, OraOrderN A} := {
    (* setoids *)
    mixin_ora_op_ne (x : A) : NonExpansive (op x);
    mixin_ora_pcore_ne n x y cx :
      x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy;
    mixin_ora_validN_ne n : Proper (dist n ==> impl) (validN n);
    mixin_ora_pcore_increasing x cx : pcore x = Some cx → Increasing cx;
    (* valid *)
    mixin_ora_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x;
    mixin_ora_validN_S n x : ✓{S n} x → ✓{n} x;
    (* monoid *)
    mixin_ora_assoc : Assoc (≡) (⋅);
    mixin_ora_comm : Comm (≡) (⋅);
    mixin_ora_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x;
    mixin_ora_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx;
    mixin_ora_pcore_monoN n x y cx :
      x ≼ₒ{n} y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ{n} cy;
    mixin_ora_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x;
    mixin_ora_extend n x y1 y2 :
      ✓{n} x → y1 ⋅ y2 ≼ₒ{n} x →
      ∃ z1 z2, z1 ⋅ z2 ≼ₒ{S n} x ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2;
    (* OraOrder *)
    mixin_ora_dist_orderN n x y : x ≡{n}≡ y → x ≼ₒ{n} y;
    mixin_ora_orderN_S n x y : x ≼ₒ{S n} y → x ≼ₒ{n} y;
    mixin_ora_orderN_trans n : Transitive (≼ₒ{n});
    mixin_ora_orderN_op n x x' y : x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y;
    mixin_ora_validN_orderN n x y : ✓{n} x → y ≼ₒ{n} x → ✓{n} y;
    mixin_ora_order_orderN x y : x ≼ₒ y ↔ (∀ n, x ≼ₒ{n} y);
    mixin_ora_pcore_order_op x cx y :
      pcore x = Some cx → ∃ cxy, pcore (x ⋅ y) = Some cxy ∧ cx ≼ₒ cxy
  }.
End mixin.

(** Bundeled version *)
Structure oraT := OraT' {
  ora_car :> Type;
  ora_equiv : Equiv ora_car;
  ora_dist : Dist ora_car;
  ora_pcore : PCore ora_car;
  ora_op : Op ora_car;
  ora_valid : Valid ora_car;
  ora_validN : ValidN ora_car;
  ora_order : OraOrder ora_car;
  ora_orderN : OraOrderN ora_car;
  ora_ofe_mixin : OfeMixin ora_car;
  ora_mixin : OraMixin ora_car;
  _ : Type
}.
Arguments OraT' _ {_ _ _ _ _ _ _ _} _ _ _.
(* Given [m : OraMixin A], the notation [OraT A m] provides a smart
constructor, which uses [ofe_mixin_of A] to infer the canonical OFE mixin of
the type [A], so that it does not have to be given manually. *)
Notation OraT A m := (OraT' A (ofe_mixin_of A%type) m A) (only parsing).

Arguments ora_car : simpl never.
Arguments ora_equiv : simpl never.
Arguments ora_dist : simpl never.
Arguments ora_pcore : simpl never.
Arguments ora_op : simpl never.
Arguments ora_valid : simpl never.
Arguments ora_validN : simpl never.
Arguments ora_order : simpl never.
Arguments ora_orderN : simpl never.
Arguments ora_ofe_mixin : simpl never.
Arguments ora_mixin : simpl never.
Add Printing Constructor oraT.
Hint Extern 0 (PCore _) => eapply (@ora_pcore _) : typeclass_instances.
Hint Extern 0 (Op _) => eapply (@ora_op _) : typeclass_instances.
Hint Extern 0 (Valid _) => eapply (@ora_valid _) : typeclass_instances.
Hint Extern 0 (ValidN _) => eapply (@ora_validN _) : typeclass_instances.
Hint Extern 0 (OraOrder _) => eapply (@ora_order _) : typeclass_instances.
Hint Extern 0 (OraOrderN _) => eapply (@ora_orderN _) : typeclass_instances.
Coercion ora_ofeC (A : oraT) : ofeT := OfeT A (ora_ofe_mixin A).
Canonical Structure ora_ofeC.

Definition ora_mixin_of' A {Ac : oraT} (f : Ac → A) : OraMixin Ac := ora_mixin Ac.
Notation ora_mixin_of A :=
  ltac:(let H := eval hnf in (ora_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ora_mixin.
  Context {A : oraT}.
  Implicit Types x y : A.
  Global Instance ora_op_ne (x : A) : NonExpansive (op x).
  Proof. apply (mixin_ora_op_ne _ (ora_mixin A)). Qed.
  Lemma ora_pcore_ne n x y cx :
    x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy.
  Proof. apply (mixin_ora_pcore_ne _ (ora_mixin A)). Qed.
  Global Instance ora_validN_ne n : Proper (dist n ==> impl) (@validN A _ n).
  Proof. apply (mixin_ora_validN_ne _ (ora_mixin A)). Qed.
  Global Instance ora_pcore_increasing x cx : pcore x = Some cx → Increasing cx.
  Proof. apply (mixin_ora_pcore_increasing _ (ora_mixin A)). Qed.
  Lemma ora_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x.
  Proof. apply (mixin_ora_valid_validN _ (ora_mixin A)). Qed.
  Lemma ora_validN_S n x : ✓{S n} x → ✓{n} x.
  Proof. apply (mixin_ora_validN_S _ (ora_mixin A)). Qed.
  Global Instance ora_assoc : Assoc (≡) (@op A _).
  Proof. apply (mixin_ora_assoc _ (ora_mixin A)). Qed.
  Global Instance ora_comm : Comm (≡) (@op A _).
  Proof. apply (mixin_ora_comm _ (ora_mixin A)). Qed.
  Lemma ora_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x.
  Proof. apply (mixin_ora_pcore_l _ (ora_mixin A)). Qed.
  Lemma ora_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx.
  Proof. apply (mixin_ora_pcore_idemp _ (ora_mixin A)). Qed.
  Lemma ora_pcore_monoN n x y cx :
    x ≼ₒ{n} y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ{n} cy.
  Proof. apply (mixin_ora_pcore_monoN _ (ora_mixin A)). Qed.
  Lemma ora_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x.
  Proof. apply (mixin_ora_validN_op_l _ (ora_mixin A)). Qed.
  Lemma ora_extend n x y1 y2 :
    ✓{n} x → y1 ⋅ y2 ≼ₒ{n} x →
    ∃ z1 z2, z1 ⋅ z2 ≼ₒ{S n} x ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2.
  Proof. apply (mixin_ora_extend _ (ora_mixin A)). Qed.
  Lemma ora_dist_orderN n x y : x ≡{n}≡ y → x ≼ₒ{n} y.
  Proof. apply (mixin_ora_dist_orderN _ (ora_mixin A)). Qed.
  Lemma ora_orderN_S n x y : x ≼ₒ{S n} y → x ≼ₒ{n} y.
  Proof. apply (mixin_ora_orderN_S _ (ora_mixin A)). Qed.
  Global Instance ora_orderN_trans n : Transitive (@OraorderN A _ n).
  Proof. apply (mixin_ora_orderN_trans _ (ora_mixin A)). Qed.
  Lemma ora_orderN_op n x x' y : x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y.
  Proof. apply (mixin_ora_orderN_op _ (ora_mixin A)). Qed.
  Lemma ora_validN_orderN n x y : ✓{n} x → y ≼ₒ{n} x → ✓{n} y.
  Proof. apply (mixin_ora_validN_orderN _ (ora_mixin A)). Qed.
  Lemma ora_order_orderN x y : x ≼ₒ y ↔ (∀ n, x ≼ₒ{n} y).
  Proof. apply (mixin_ora_order_orderN _ (ora_mixin A)). Qed.
  Lemma ora_pcore_order_op x cx y :
    pcore x = Some cx → ∃ cxy, pcore (x ⋅ y) = Some cxy ∧ cx ≼ₒ cxy.
  Proof. apply (mixin_ora_pcore_order_op _ (ora_mixin A)). Qed.
End ora_mixin.

Definition OraopM {A : oraT} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅ₒ?" := OraopM (at level 50, left associativity) : stdpp_scope.

(** * CoreId elements *)
Class OraCoreId {A : oraT} (x : A) := oracore_id : pcore x ≡ Some x.
Arguments oracore_id {_} _ {_}.
Hint Mode OraCoreId + ! : typeclass_instances.
Instance: Params (@OraCoreId) 1.

(** * Exclusive elements (i.e., elements that cannot have a frame). *)
Class OraExclusive {A : oraT} (x : A) := oraexclusive0_l y : ✓{0} (x ⋅ y) → False.
Arguments oraexclusive0_l {_} _ {_} _ _.
Hint Mode OraExclusive + ! : typeclass_instances.
Instance: Params (@OraExclusive) 1.

(** * Cancelable elements. *)
Class OraCancelable {A : oraT} (x : A) :=
  oracancelableN n y z : ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ≡{n}≡ z.
Arguments oracancelableN {_} _ {_} _ _ _ _.
Hint Mode OraCancelable + ! : typeclass_instances.
Instance: Params (@OraCancelable) 1.

(** * Identity-free elements. *)
Class OraIdFree {A : oraT} (x : A) :=
  oraid_free0_r y : ✓{0}x → x ⋅ y ≡{0}≡ x → False.
Arguments oraid_free0_r {_} _ {_} _ _.
Hint Mode OraIdFree + ! : typeclass_instances.
Instance: Params (@OraIdFree) 1.

(** * CMRAs whose core is total *)
(** The function [core] may return a dummy when used on CMRAs without total
core. *)
Class OraTotal (A : oraT) := ora_total (x : A) : is_Some (pcore x).
Hint Mode OraTotal ! : typeclass_instances.

Structure uoraT := UoraT' {
  uora_car :> Type;
  uora_equiv : Equiv uora_car;
  uora_dist : Dist uora_car;
  uora_pcore : PCore uora_car;
  uora_op : Op uora_car;
  uora_valid : Valid uora_car;
  uora_validN : ValidN uora_car;
  uora_order : OraOrder uora_car;
  uora_orderN : OraOrderN uora_car;
  uora_unit : Unit uora_car;
  uora_ofe_mixin : OfeMixin uora_car;
  uora_ora_mixin : OraMixin uora_car;
  uora_mixin : UcmraMixin uora_car;
  _ : Type;
}.
Arguments UoraT' _ {_ _ _ _ _ _ _} _ _ _ _.
Notation UoraT A m :=
  (UoraT' A (ofe_mixin_of A%type) (ora_mixin_of A%type) m A%type) (only parsing).
Arguments uora_car : simpl never.
Arguments uora_equiv : simpl never.
Arguments uora_dist : simpl never.
Arguments uora_pcore : simpl never.
Arguments uora_op : simpl never.
Arguments uora_valid : simpl never.
Arguments uora_validN : simpl never.
Arguments uora_order : simpl never.
Arguments uora_orderN : simpl never.
Arguments uora_ofe_mixin : simpl never.
Arguments uora_ora_mixin : simpl never.
Arguments uora_mixin : simpl never.
Add Printing Constructor uoraT.
Hint Extern 0 (Unit _) => eapply (@uora_unit _) : typeclass_instances.
Coercion uora_ofeC (A : uoraT) : ofeT := OfeT A (uora_ofe_mixin A).
Canonical Structure uora_ofeC.
Coercion uora_cmraR (A : uoraT) : oraT :=
  OraT' A (uora_ofe_mixin A) (uora_ora_mixin A) A.
Canonical Structure uora_cmraR.

(** Lifting properties from the mixin *)
Section uora_mixin.
  Context {A : uoraT}.
  Implicit Types x y : A.
  Lemma uora_unit_valid : ✓ (ε : A).
  Proof. apply (mixin_ucmra_unit_valid _ (uora_mixin A)). Qed.
  Global Instance uora_unit_left_id : LeftId (≡) ε (@op A _).
  Proof. apply (mixin_ucmra_unit_left_id _ (uora_mixin A)). Qed.
  Lemma uora_pcore_unit : pcore (ε:A) ≡ Some ε.
  Proof. apply (mixin_ucmra_pcore_unit _ (uora_mixin A)). Qed.
End uora_mixin.

(** * Discrete CMRAs *)
Class OraDiscrete (A : oraT) := {
  ora_discrete_ofe_discrete :> OfeDiscrete A;
  ora_discrete_valid (x : A) : ✓{0} x → ✓ x;
  ora_discrete_order (x y: A) : x ≼ₒ{0} y → x ≼ₒ y
}.
Hint Mode OraDiscrete ! : typeclass_instances.

(** * Morphisms *)
Class OraMorphism {A B : oraT} (f : A → B) := {
  ora_morphism_ne :> NonExpansive f;
  ora_morphism_validN n x : ✓{n} x → ✓{n} f x;
  ora_morphism_orderN n x y : x ≼ₒ{n} y  → f x ≼ₒ{n} f y;
  ora_morphism_pcore x : pcore (f x) ≡ f <$> pcore x;
  ora_morphism_op x y : f x ⋅ f y ≡ f (x ⋅ y)
}.
Arguments ora_morphism_validN {_ _} _ {_} _ _ _.
Arguments ora_morphism_orderN {_ _} _ {_} _ _ _.
Arguments ora_morphism_pcore {_ _} _ {_} _.
Arguments ora_morphism_op {_ _} _ {_} _ _.

(** * Properties **)
Section ora.
Context {A : oraT}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Global Instance ora_included_trans: Transitive (@Oraorder A _).
Proof.
  intros x y z Hxy Hyz; apply ora_order_orderN => n;
    eapply (@ora_orderN_trans _ _ _ y); by eapply ora_order_orderN.
Qed.
Global Instance ora_pcore_ne' : NonExpansive (@pcore A _).
Proof.
  intros n x y Hxy. destruct (pcore x) as [cx|] eqn:?.
  { destruct (ora_pcore_ne n x y cx) as (cy&->&->); auto. }
  destruct (pcore y) as [cy|] eqn:?; auto.
  destruct (ora_pcore_ne n y x cy) as (cx&?&->); simplify_eq/=; auto.
Qed.
Lemma ora_pcore_proper x y cx :
  x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy.
Proof.
  intros. destruct (ora_pcore_ne 0 x y cx) as (cy&?&?); auto.
  exists cy; split; [done|apply equiv_dist=> n].
  destruct (ora_pcore_ne n x y cx) as (cy'&?&?); naive_solver.
Qed.
Global Instance ora_pcore_proper' : Proper ((≡) ==> (≡)) (@pcore A _).
Proof. apply (ne_proper _). Qed.
Global Instance ora_op_ne' : NonExpansive2 (@op A _).
Proof. intros n x1 x2 Hx y1 y2 Hy. by rewrite Hy (comm _ x1) Hx (comm _ y2). Qed.
Global Instance ora_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (@op A _).
Proof. apply (ne_proper_2 _). Qed.
Global Instance ora_validN_ne' : Proper (dist n ==> iff) (@validN A _ n) | 1.
Proof. by split; apply ora_validN_ne. Qed.
Global Instance ora_validN_proper : Proper ((≡) ==> iff) (@validN A _ n) | 1.
Proof. by intros n x1 x2 Hx; apply ora_validN_ne', equiv_dist. Qed.

Lemma ora_order_op x x' y : x ≼ₒ x' → x ⋅ y ≼ₒ x' ⋅ y.
Proof.
  intros. apply ora_order_orderN =>?.
  by eapply ora_orderN_op, ora_order_orderN.
Qed.

Global Instance ora_valid_proper : Proper ((≡) ==> iff) (@valid A _).
Proof.
  intros x y Hxy; rewrite !ora_valid_validN.
  by split=> ? n; [rewrite -Hxy|rewrite Hxy].
Qed.
Global Instance ora_orderN_ne n :
  Proper (dist n ==> dist n ==> iff) (@OraorderN A _ n) | 1.
Proof.
  intros x x' Hx y y' Hy. split.
  - intros Hxy. etrans; first apply ora_dist_orderN; first by rewrite -Hx.
    etrans; first done. by apply ora_dist_orderN.
  - intros Hxy'. etrans; first apply ora_dist_orderN; first done.
    etrans; first done. by apply ora_dist_orderN.
Qed.
Global Instance ora_orderN_proper n :
  Proper ((≡) ==> (≡) ==> iff) (@OraorderN A _ n) | 1.
Proof.
  intros x x' Hx y y' Hy; revert Hx Hy; rewrite !equiv_dist=> Hx Hy.
  by rewrite (Hx n) (Hy n).
Qed.
Global Instance ora_order_proper :
  Proper ((≡) ==> (≡) ==> iff) (@Oraorder A _) | 1.
Proof.
  intros x x' Hx y y' Hy.
  split; intros Hxy; apply ora_order_orderN => n;
    eapply (ora_order_orderN) in Hxy.
  - eapply ora_orderN_proper; [symmetry| symmetry|]; eauto.
  - eapply ora_orderN_proper; eauto.
Qed.
Global Instance ora_orderN_properN n :
  Proper (flip (≼ₒ{n}) ==> (≼ₒ{n}) ==> impl) (@OraorderN A _ n) | 1.
Proof.
  intros x x' Hx y y' Hy Hz.
  etrans; first apply Hx. etrans; eauto.
Qed.
Global Instance ora_order_properN :
  Proper (flip (≼ₒ) ==> (≼ₒ) ==> impl) (@Oraorder A _) | 1.
Proof.
  intros x x' Hx y y' Hy Hz.
  etrans; first apply Hx. etrans; eauto.
Qed.
Global Instance ora_opM_ne : NonExpansive2 (@OraopM A).
Proof. destruct 2; by ofe_subst. Qed.
Global Instance ora_opM_proper : Proper ((≡) ==> (≡) ==> (≡)) (@OraopM A).
Proof. destruct 2; by setoid_subst. Qed.

Global Instance CoreId_proper : Proper ((≡) ==> iff) (@OraCoreId A).
Proof. solve_proper. Qed.
Global Instance Exclusive_proper : Proper ((≡) ==> iff) (@OraExclusive A).
Proof. intros x y Hxy. rewrite /OraExclusive. by setoid_rewrite Hxy. Qed.
Global Instance Cancelable_proper : Proper ((≡) ==> iff) (@OraCancelable A).
Proof. intros x y Hxy. rewrite /OraCancelable. by setoid_rewrite Hxy. Qed.
Global Instance IdFree_proper : Proper ((≡) ==> iff) (@OraIdFree A).
Proof. intros x y Hxy. rewrite /OraIdFree. by setoid_rewrite Hxy. Qed.

(** ** Op *)
Lemma ora_opM_assoc x y mz : (x ⋅ y) ⋅ₒ? mz ≡ x ⋅ (y ⋅ₒ? mz).
Proof. destruct mz; by rewrite /= -?assoc. Qed.

(** ** Validity *)
Lemma ora_validN_le n n' x : ✓{n} x → n' ≤ n → ✓{n'} x.
Proof. induction 2; eauto using ora_validN_S. Qed.
Lemma ora_valid_op_l x y : ✓ (x ⋅ y) → ✓ x.
Proof. rewrite !ora_valid_validN; eauto using ora_validN_op_l. Qed.
Lemma ora_validN_op_r n x y : ✓{n} (x ⋅ y) → ✓{n} y.
Proof. rewrite (comm _ x); apply ora_validN_op_l. Qed.
Lemma ora_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite !ora_valid_validN; eauto using ora_validN_op_r. Qed.

(** ** Core *)
Lemma ora_pcore_l' x cx : pcore x ≡ Some cx → cx ⋅ x ≡ x.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. by apply ora_pcore_l. Qed.
Lemma ora_pcore_r x cx : pcore x = Some cx → x ⋅ cx ≡ x.
Proof. intros. rewrite comm. by apply ora_pcore_l. Qed.
Lemma ora_pcore_r' x cx : pcore x ≡ Some cx → x ⋅ cx ≡ x.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. by apply ora_pcore_r. Qed.
Lemma ora_pcore_idemp' x cx : pcore x ≡ Some cx → pcore cx ≡ Some cx.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. eauto using ora_pcore_idemp. Qed.
Lemma ora_pcore_dup x cx : pcore x = Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using ora_pcore_r', ora_pcore_idemp. Qed.
Lemma ora_pcore_dup' x cx : pcore x ≡ Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using ora_pcore_r', ora_pcore_idemp'. Qed.
Lemma ora_pcore_validN n x cx : ✓{n} x → pcore x = Some cx → ✓{n} cx.
Proof.
  intros Hvx Hx%ora_pcore_l. move: Hvx; rewrite -Hx. apply ora_validN_op_l.
Qed.
Lemma ora_pcore_valid x cx : ✓ x → pcore x = Some cx → ✓ cx.
Proof.
  intros Hv Hx%ora_pcore_l. move: Hv; rewrite -Hx. apply ora_valid_op_l.
Qed.

(** ** CoreId elements *)
Lemma core_id_dup x `{!OraCoreId x} : x ≡ x ⋅ x.
Proof. by apply ora_pcore_dup' with x. Qed.

(** ** Exclusive elements *)
Lemma OraexclusiveN_l n x `{!OraExclusive x} y : ✓{n} (x ⋅ y) → False.
Proof. intros. eapply (oraexclusive0_l x y), ora_validN_le; eauto with lia. Qed.
Lemma OraexclusiveN_r n x `{!OraExclusive x} y : ✓{n} (y ⋅ x) → False.
Proof. rewrite comm. by apply OraexclusiveN_l. Qed.
Lemma Oraexclusive_l x `{!OraExclusive x} y : ✓ (x ⋅ y) → False.
Proof. by move /ora_valid_validN /(_ 0) /oraexclusive0_l. Qed.
Lemma Oraexclusive_r x `{!OraExclusive x} y : ✓ (y ⋅ x) → False.
Proof. rewrite comm. by apply Oraexclusive_l. Qed.
Lemma OraexclusiveN_opM n x `{!OraExclusive x} my : ✓{n} (x ⋅ₒ? my) → my = None.
Proof. destruct my as [y|]. move=> /(OraexclusiveN_l _ x) []. done. Qed.
(* Lemma Oraexclusive_includedN n x `{!OraExclusive x} y : x ≼ₒ{n} y → ✓{n} y → False. *)
(* Proof. intros [? ->]. by apply OraexclusiveN_l. Qed. *)
(* Lemma Oraexclusive_included x `{!OraExclusive x} y : x ≼ y → ✓ y → False. *)
(* Proof. intros [? ->]. by apply Oraexclusive_l. Qed. *)

(** ** Order *)
Lemma ora_valid_order x y : ✓ y → x ≼ y → ✓ x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using ora_valid_op_l. Qed.
Lemma ora_validN_order n x y : ✓{n} y → x ≼ y → ✓{n} x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using ora_validN_op_l. Qed.

Lemma ora_orderN_le n n' x y : x ≼ₒ{n} y → n' ≤ n → x ≼ₒ{n'} y.
Proof. induction 2; auto using ora_orderN_S. Qed.

Lemma ora_pcore_order_op' x cx y :
  pcore x ≡ Some cx → ∃ cxy, pcore (x ⋅ y) = Some cxy ∧ cx ≼ₒ cxy.
Proof.
  intros (cx'&?&Hcx)%equiv_Some_inv_r'.
  destruct (ora_pcore_order_op x cx' y) as (cy&->&?); auto.
  exists cy; by rewrite Hcx.
 Qed.

Global Instance ora_orderN_refl n: Reflexive ((≼ₒ{n}) : A → A → Prop).
Proof. intros ?; by apply ora_dist_orderN. Qed.

Lemma ora_order_refl : Reflexive ((≼ₒ) : A → A → Prop).
Proof. intros x. by eapply ora_order_orderN. Qed.

Lemma ora_pcore_monoN' n x y cx :
  x ≼ₒ{n} y → pcore x ≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ{n} cy.
Proof.
  intros ? (cx'&?&Hcx)%equiv_Some_inv_r'.
  destruct (ora_pcore_monoN n x y cx') as (cy&->&?); auto.
  exists cy; by rewrite Hcx.
Qed.
(* Lemma cmra_pcore_monoN' n x y cx : *)
(*   x ≼{n} y → pcore x ≡{n}≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼{n} cy. *)
(* Proof. *)
(*   intros [z Hy] (cx'&?&Hcx)%dist_Some_inv_r'. *)
(*   destruct (cmra_pcore_mono x (x ⋅ z) cx') *)
(*     as (cy&Hxy&?); auto using cmra_included_l. *)
(*   assert (pcore y ≡{n}≡ Some cy) as (cy'&?&Hcy')%dist_Some_inv_r'. *)
(*   { by rewrite Hy Hxy. } *)
(*   exists cy'; split; first done. *)
(*   rewrite Hcx -Hcy'; auto using cmra_included_includedN. *)
(* Qed. *)
(* Lemma ora_order_pcore x cx : pcore x = Some cx → cx ≼ₒ x. *)
(* Proof. exists x. by rewrite ora_pcore_l. Qed. *)

Lemma ora_monoN_l n x y z : x ≼ₒ{n} y → z ⋅ x ≼ₒ{n} z ⋅ y.
Proof. rewrite !(comm _ z) => ?. by apply ora_orderN_op. Qed.
Lemma ora_mono_l x y z : x ≼ₒ y → z ⋅ x ≼ₒ z ⋅ y.
Proof.
  rewrite !(comm _ z) => ?.
  apply ora_order_orderN =>?; apply ora_orderN_op.
  by apply ora_order_orderN.
Qed.
Lemma ora_monoN_r n x y z : x ≼ₒ{n} y → x ⋅ z ≼ₒ{n} y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply ora_monoN_l. Qed.
Lemma ora_mono_r x y z : x ≼ₒ y → x ⋅ z ≼ₒ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply ora_mono_l. Qed.
Lemma ora_monoN n x1 x2 y1 y2 : x1 ≼ₒ{n} y1 → x2 ≼ₒ{n} y2 → x1 ⋅ x2 ≼ₒ{n} y1 ⋅ y2.
Proof.
  intros; etrans; first apply ora_monoN_l; eauto.
  eauto using ora_monoN_r.
Qed.
Lemma ora_mono x1 x2 y1 y2 : x1 ≼ₒ y1 → x2 ≼ₒ y2 → x1 ⋅ x2 ≼ₒ y1 ⋅ y2.
Proof. intros; etrans; eauto using ora_mono_l, ora_mono_r. Qed.

Global Instance ora_monoN' n :
  Proper (OraorderN n ==> OraorderN n ==> OraorderN n) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply ora_monoN. Qed.
Global Instance cmra_mono' :
  Proper (Oraorder ==> Oraorder ==> Oraorder) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply ora_mono. Qed.

(* Lemma ora_order_dist_l n x1 x2 x1' : *)
(*   x1 ≼ₒ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ₒ x2' ∧ x2' ≡{n}≡ x2. *)
(* Proof. *)
(*   intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using cmra_included_l. *)
(*   by rewrite Hx1 Hx2. *)
(* Qed. *)

(** ** Total core *)
Section total_core.
  Local Set Default Proof Using "Type*".
  Context `{OraTotal A}.

  Lemma ora_core_l x : core x ⋅ x ≡ x.
  Proof.
    destruct (ora_total x) as [cx Hcx]. by rewrite /core /= Hcx ora_pcore_l.
  Qed.
  Lemma ora_core_idemp x : core (core x) ≡ core x.
  Proof.
    destruct (ora_total x) as [cx Hcx]. by rewrite /core /= Hcx ora_pcore_idemp.
  Qed.
  Lemma ora_core_mono x y : x ≼ₒ y → core x ≼ₒ core y.
  Proof.
    intros; destruct (ora_total x) as [cx Hcx].
    apply ora_order_orderN => n.
    destruct (ora_pcore_monoN n x y cx) as (cy&Hcy&?); auto;
      first by apply ora_order_orderN.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Global Instance ora_core_ne : NonExpansive (@core A _).
  Proof.
    intros n x y Hxy. destruct (ora_total x) as [cx Hcx].
    by rewrite /core /= -Hxy Hcx.
  Qed.
  Global Instance ora_core_proper : Proper ((≡) ==> (≡)) (@core A _).
  Proof. apply (ne_proper _). Qed.

  Lemma ora_core_r x : x ⋅ core x ≡ x.
  Proof. by rewrite (comm _ x) ora_core_l. Qed.
  Lemma ora_core_dup x : core x ≡ core x ⋅ core x.
  Proof. by rewrite -{3}(ora_core_idemp x) ora_core_r. Qed.
  Lemma ora_core_validN n x : ✓{n} x → ✓{n} core x.
  Proof. rewrite -{1}(ora_core_l x); apply ora_validN_op_l. Qed.
  Lemma ora_core_valid x : ✓ x → ✓ core x.
  Proof. rewrite -{1}(ora_core_l x); apply ora_valid_op_l. Qed.

  Lemma oracore_id_total x : OraCoreId x ↔ core x ≡ x.
  Proof.
    split; [intros; by rewrite /core /= (oracore_id x)|].
    rewrite /OraCoreId /core /=.
    destruct (ora_total x) as [? ->]. by constructor.
  Qed.
  Lemma oracore_id_core x `{!OraCoreId x} : core x ≡ x.
  Proof. by apply oracore_id_total. Qed.

  Global Instance ora_core_core_id x : OraCoreId (core x).
  Proof.
    destruct (ora_total x) as [cx Hcx].
    rewrite /OraCoreId /core /= Hcx /=. eauto using ora_pcore_idemp.
  Qed.

  Lemma ora_included_core x : core x ≼ x.
  Proof. by exists x; rewrite ora_core_l. Qed.
  Global Instance ora_orderN_preorder n : PreOrder (@OraorderN A _ n).
  Proof.
    split; [|apply _]; auto.
  Qed.
  Global Instance ora_order_preorder : PreOrder (@Oraorder A _).
  Proof.
    split; [|apply _]. intros x; by apply ora_order_orderN.
  Qed.
  Lemma ora_core_monoN n x y : x ≼ₒ{n} y → core x ≼ₒ{n} core y.
  Proof.
    intros Hxy.
    intros; destruct (ora_total x) as [cx Hcx].
    destruct (ora_pcore_monoN n x y cx) as (cy&Hcy&?); trivial.
    by rewrite /core /= Hcx Hcy.
  Qed.
End total_core.

(** ** Discrete *)
(* Lemma cmra_discrete_included_l x y : Discrete x → ✓{0} y → x ≼ₒ{0} y → x ≼ₒ y. *)
(* Proof. *)
(*   intros ?? [x' ?]. *)
(*   destruct (cmra_extend 0 y x x') as (z&z'&Hy&Hz&Hz'); auto; simpl in *. *)
(*   by exists z'; rewrite Hy (discrete x z). *)
(* Qed. *)
(* Lemma cmra_discrete_included_r x y : Discrete y → x ≼{0} y → x ≼ y. *)
(* Proof. intros ? [x' ?]. exists x'. by apply (discrete y). Qed. *)
(* Lemma cmra_op_discrete x1 x2 : *)
(*   ✓ (x1 ⋅ x2) → Discrete x1 → Discrete x2 → Discrete (x1 ⋅ x2). *)
(* Proof. *)
(*   intros ??? z Hz. *)
(*   destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *. *)
(*   { rewrite -?Hz. by apply cmra_valid_validN. } *)
(*   by rewrite Hz' (discrete x1 y1) // (discrete x2 y2). *)
(* Qed. *)

(** ** Discrete *)
Lemma ora_discrete_valid_iff `{OraDiscrete A} n x : ✓ x ↔ ✓{n} x.
Proof.
  split; first by rewrite ora_valid_validN.
  eauto using ora_discrete_valid, ora_validN_le with lia.
Qed.
Lemma ora_discrete_valid_iff_0 `{OraDiscrete A} n x : ✓{0} x ↔ ✓{n} x.
Proof. by rewrite -!ora_discrete_valid_iff. Qed.
Lemma ora_discrete_included_iff `{OraDiscrete A} n x y : x ≼ₒ y ↔ x ≼ₒ{n} y.
Proof.
  split => ?; first by apply ora_order_orderN.
  apply ora_discrete_order; eapply ora_orderN_le; first eauto; lia.
Qed.
Lemma cmra_discrete_included_iff_0 `{OraDiscrete A} n x y : x ≼ₒ{0} y ↔ x ≼ₒ{n} y.
Proof. by rewrite -!ora_discrete_included_iff. Qed.

(* (** Cancelable elements  *) *)
(* Global Instance cancelable_proper : Proper (equiv ==> iff) (@Cancelable A). *)
(* Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed. *)
(* Lemma cancelable x `{!Cancelable x} y z : ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z. *)
(* Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (cancelableN x). Qed. *)
(* Lemma discrete_cancelable x `{CmraDiscrete A}: *)
(*   (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z) → Cancelable x. *)
(* Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed. *)
(* Global Instance cancelable_op x y : *)
(*   Cancelable x → Cancelable y → Cancelable (x ⋅ y). *)
(* Proof. *)
(*   intros ?? n z z' ??. apply (cancelableN y), (cancelableN x). *)
(*   - eapply cmra_validN_op_r. by rewrite assoc. *)
(*   - by rewrite assoc. *)
(*   - by rewrite !assoc. *)
(* Qed. *)
(* Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x. *)
(* Proof. intros ? n z z' []%(exclusiveN_l _ x). Qed. *)

(* (** Id-free elements  *) *)
(* Global Instance id_free_ne n : Proper (dist n ==> iff) (@IdFree A). *)
(* Proof. *)
(*   intros x x' EQ%(dist_le _ 0); last lia. rewrite /IdFree. *)
(*   split=> y ?; (rewrite -EQ || rewrite EQ); eauto. *)
(* Qed. *)
(* Global Instance id_free_proper : Proper (equiv ==> iff) (@IdFree A). *)
(* Proof. by move=> P Q /equiv_dist /(_ 0)=> ->. Qed. *)
(* Lemma id_freeN_r n n' x `{!IdFree x} y : ✓{n}x → x ⋅ y ≡{n'}≡ x → False. *)
(* Proof. eauto using cmra_validN_le, dist_le with lia. Qed. *)
(* Lemma id_freeN_l n n' x `{!IdFree x} y : ✓{n}x → y ⋅ x ≡{n'}≡ x → False. *)
(* Proof. rewrite comm. eauto using id_freeN_r. Qed. *)
(* Lemma id_free_r x `{!IdFree x} y : ✓x → x ⋅ y ≡ x → False. *)
(* Proof. move=> /cmra_valid_validN ? /equiv_dist. eauto. Qed. *)
(* Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x ≡ x → False. *)
(* Proof. rewrite comm. eauto using id_free_r. Qed. *)
(* Lemma discrete_id_free x `{CmraDiscrete A}: *)
(*   (∀ y, ✓ x → x ⋅ y ≡ x → False) → IdFree x. *)
(* Proof. *)
(*   intros Hx y ??. apply (Hx y), (discrete _); eauto using cmra_discrete_valid. *)
(* Qed. *)
(* Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y). *)
(* Proof. *)
(*   intros ?? z ? Hid%symmetry. revert Hid. rewrite -assoc=>/(cancelableN x) ?. *)
(*   eapply (id_free0_r _); [by eapply cmra_validN_op_r |symmetry; eauto]. *)
(* Qed. *)
(* Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y). *)
(* Proof. intros. rewrite comm. apply _. Qed. *)
(* Global Instance exclusive_id_free x : Exclusive x → IdFree x. *)
(* Proof. intros ? z ? Hid. apply (exclusiveN_l 0 x z). by rewrite Hid. Qed. *)
End ora.

(** * Properties about CMRAs with a unit element **)
Section uora.
  Context {A : uoraT}.
  Implicit Types x y z : A.

  Lemma uora_unit_validN n : ✓{n} (ε:A).
  Proof. apply ora_valid_validN, uora_unit_valid. Qed.
  Global Instance uora_unit_right_id : RightId (≡) ε (@op A _).
  Proof. by intros x; rewrite (comm op) left_id. Qed.
  Global Instance uora_unit_core_id : OraCoreId (ε:A).
  Proof. apply uora_pcore_unit. Qed.

  Lemma uora_unit_order_increasing x `{!Increasing x} : ε ≼ₒ x.
  Proof.
    setoid_replace x with (x ⋅ ε) by by rewrite right_id.
    apply (increasing _).
  Qed.

  Global Instance uora_increasing_order_unit x : ε ≼ₒ x → Increasing x.
  Proof.
    intros Hx y.
    setoid_replace y with (ε ⋅ y) at 1 by by rewrite left_id.
    apply ora_order_op; auto.
  Qed.

  Lemma uora_unit_order_pcore x y : pcore x = Some y → ε ≼ₒ y.
  Proof.
    intros; eapply (@uora_unit_order_increasing _ _).
  Qed.

  Global Instance uora_unit_ora_total : OraTotal A.
  Proof.
    intros x.
    destruct (ora_pcore_order_op' ε ε x) as (?&Hc&_).
    apply uora_pcore_unit.
    rewrite -(left_id _ _ x) Hc; eauto.
  Qed.

  Lemma uora_unit_order_core x : ε ≼ₒ core x.
  Proof.
    destruct (ora_total x) as [z Heq]; rewrite /core /core' Heq /=.
    apply (@uora_unit_order_increasing _ _).
  Qed.

  Lemma uora_core_order_op x y : core x ≼ₒ core (x ⋅ y).
  Proof.
    destruct (ora_total x) as [z Heq]; rewrite /core /core' Heq /=.
    destruct (ora_pcore_order_op x z y) as (cxy&Hcxy&?); auto.
    by rewrite Hcxy /=.
  Qed.

  Global Instance empty_oracancelable : OraCancelable (ε:A).
  Proof. intros ???. by rewrite !left_id. Qed.

  (* For big ops *)
  Global Instance cmra_monoid : Monoid (@op A _) := {| monoid_unit := ε |}.
End uora.

(* Hint Immediate cmra_unit_cmra_total. *)

(* (** * Properties about CMRAs with Leibniz equality *) *)
(* Section cmra_leibniz. *)
(*   Local Set Default Proof Using "Type*". *)
(*   Context {A : cmraT} `{!LeibnizEquiv A}. *)
(*   Implicit Types x y : A. *)

(*   Global Instance cmra_assoc_L : Assoc (=) (@op A _). *)
(*   Proof. intros x y z. unfold_leibniz. by rewrite assoc. Qed. *)
(*   Global Instance cmra_comm_L : Comm (=) (@op A _). *)
(*   Proof. intros x y. unfold_leibniz. by rewrite comm. Qed. *)

(*   Lemma cmra_pcore_l_L x cx : pcore x = Some cx → cx ⋅ x = x. *)
(*   Proof. unfold_leibniz. apply cmra_pcore_l'. Qed. *)
(*   Lemma cmra_pcore_idemp_L x cx : pcore x = Some cx → pcore cx = Some cx. *)
(*   Proof. unfold_leibniz. apply cmra_pcore_idemp'. Qed. *)

(*   Lemma cmra_opM_assoc_L x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz). *)
(*   Proof. unfold_leibniz. apply cmra_opM_assoc. Qed. *)

(*   (** ** Core *) *)
(*   Lemma cmra_pcore_r_L x cx : pcore x = Some cx → x ⋅ cx = x. *)
(*   Proof. unfold_leibniz. apply cmra_pcore_r'. Qed. *)
(*   Lemma cmra_pcore_dup_L x cx : pcore x = Some cx → cx = cx ⋅ cx. *)
(*   Proof. unfold_leibniz. apply cmra_pcore_dup'. Qed. *)

(*   (** ** CoreId elements *) *)
(*   Lemma core_id_dup_L x `{!CoreId x} : x = x ⋅ x. *)
(*   Proof. unfold_leibniz. by apply core_id_dup. Qed. *)

(*   (** ** Total core *) *)
(*   Section total_core. *)
(*     Context `{CmraTotal A}. *)

(*     Lemma cmra_core_r_L x : x ⋅ core x = x. *)
(*     Proof. unfold_leibniz. apply cmra_core_r. Qed. *)
(*     Lemma cmra_core_l_L x : core x ⋅ x = x. *)
(*     Proof. unfold_leibniz. apply cmra_core_l. Qed. *)
(*     Lemma cmra_core_idemp_L x : core (core x) = core x. *)
(*     Proof. unfold_leibniz. apply cmra_core_idemp. Qed. *)
(*     Lemma cmra_core_dup_L x : core x = core x ⋅ core x. *)
(*     Proof. unfold_leibniz. apply cmra_core_dup. Qed. *)
(*     Lemma core_id_total_L x : CoreId x ↔ core x = x. *)
(*     Proof. unfold_leibniz. apply core_id_total. Qed. *)
(*     Lemma core_id_core_L x `{!CoreId x} : core x = x. *)
(*     Proof. by apply core_id_total_L. Qed. *)
(*   End total_core. *)
(* End cmra_leibniz. *)

(* Section ucmra_leibniz. *)
(*   Local Set Default Proof Using "Type*". *)
(*   Context {A : ucmraT} `{!LeibnizEquiv A}. *)
(*   Implicit Types x y z : A. *)

(*   Global Instance ucmra_unit_left_id_L : LeftId (=) ε (@op A _). *)
(*   Proof. intros x. unfold_leibniz. by rewrite left_id. Qed. *)
(*   Global Instance ucmra_unit_right_id_L : RightId (=) ε (@op A _). *)
(*   Proof. intros x. unfold_leibniz. by rewrite right_id. Qed. *)
(* End ucmra_leibniz. *)

(* (** * Constructing a CMRA with total core *) *)
(* Section cmra_total. *)
(*   Context A `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A}. *)
(*   Context (total : ∀ x : A, is_Some (pcore x)). *)
(*   Context (op_ne : ∀ x : A, NonExpansive (op x)). *)
(*   Context (core_ne : NonExpansive (@core A _)). *)
(*   Context (validN_ne : ∀ n, Proper (dist n ==> impl) (@validN A _ n)). *)
(*   Context (valid_validN : ∀ (x : A), ✓ x ↔ ∀ n, ✓{n} x). *)
(*   Context (validN_S : ∀ n (x : A), ✓{S n} x → ✓{n} x). *)
(*   Context (op_assoc : Assoc (≡) (@op A _)). *)
(*   Context (op_comm : Comm (≡) (@op A _)). *)
(*   Context (core_l : ∀ x : A, core x ⋅ x ≡ x). *)
(*   Context (core_idemp : ∀ x : A, core (core x) ≡ core x). *)
(*   Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y). *)
(*   Context (validN_op_l : ∀ n (x y : A), ✓{n} (x ⋅ y) → ✓{n} x). *)
(*   Context (extend : ∀ n (x y1 y2 : A), *)
(*     ✓{n} x → x ≡{n}≡ y1 ⋅ y2 → *)
(*     ∃ z1 z2, x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2). *)
(*   Lemma cmra_total_mixin : CmraMixin A. *)
(*   Proof using Type*. *)
(*     split; auto. *)
(*     - intros n x y ? Hcx%core_ne Hx; move: Hcx. rewrite /core /= Hx /=. *)
(*       case (total y)=> [cy ->]; eauto. *)
(*     - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx. *)
(*     - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=. *)
(*       case (total cx)=>[ccx ->]; by constructor. *)
(*     - intros x y cx Hxy%core_mono Hx. move: Hxy. *)
(*       rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto. *)
(*   Qed. *)
(* End cmra_total. *)

(** * Properties about morphisms *)
Instance ora_morphism_id {A : oraT} : OraMorphism (@id A).
Proof. split=>//=. apply _. intros. by rewrite option_fmap_id. Qed.
Instance ora_morphism_proper {A B : oraT} (f : A → B) `{!OraMorphism f} :
  Proper ((≡) ==> (≡)) f := ne_proper _.
Instance ora_morphism_compose {A B C : oraT} (f : A → B) (g : B → C) :
  OraMorphism f → OraMorphism g → OraMorphism (g ∘ f).
Proof.
  split.
  - apply _.
  - move=> n x Hx /=. by apply ora_morphism_validN, ora_morphism_validN.
  - move=> n x Hx Hle /=. by apply ora_morphism_orderN, ora_morphism_orderN.
  - move=> x /=. by rewrite 2!ora_morphism_pcore option_fmap_compose.
  - move=> x y /=. by rewrite !ora_morphism_op.
Qed.

Section ora_morphism.
  Local Set Default Proof Using "Type*".
  Context {A B : oraT} (f : A → B) `{!OraMorphism f}.
  Lemma ora_morphism_core x : core (f x) ≡ f (core x).
  Proof. unfold core, core'. rewrite ora_morphism_pcore. by destruct (pcore x). Qed.
  Lemma ora_morphism_monotone x y : x ≼ₒ y → f x ≼ₒ f y.
  Proof.
    intros Hle. apply ora_order_orderN => n. apply ora_morphism_orderN; eauto.
    by eapply ora_order_orderN in Hle.
  Qed.
  Lemma ora_morphism_monotoneN n x y : x ≼ₒ{n} y → f x ≼ₒ{n} f y.
  Proof. by apply ora_morphism_orderN. Qed.
  Lemma cmra_monotone_valid x : ✓ x → ✓ f x.
  Proof. rewrite !ora_valid_validN; eauto using ora_morphism_validN. Qed.
End ora_morphism.

(** Functors *)
Structure OrarFunctor := OraRFunctor {
  orarFunctor_car : ofeT → ofeT → oraT;
  orarFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → orarFunctor_car A1 B1 -n> orarFunctor_car A2 B2;
  orarFunctor_ne A1 A2 B1 B2 :
    NonExpansive (@orarFunctor_map A1 A2 B1 B2);
  orarFunctor_id {A B} (x : orarFunctor_car A B) : orarFunctor_map (cid,cid) x ≡ x;
  orarFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    orarFunctor_map (f◎g, g'◎f') x ≡ orarFunctor_map (g,g') (orarFunctor_map (f,f') x);
  orarFunctor_mor {A1 A2 B1 B2} (fg : (A2 -n> A1) * (B1 -n> B2)) :
    OraMorphism (orarFunctor_map fg)
}.
Existing Instances orarFunctor_ne orarFunctor_mor.
Instance: Params (@orarFunctor_map) 5.

Delimit Scope orarFunctor_scope with RF.
Bind Scope orarFunctor_scope with rFunctor.

Class OrarFunctorContractive (F : OrarFunctor) :=
  rFunctor_contractive A1 A2 B1 B2 :> Contractive (@orarFunctor_map F A1 A2 B1 B2).

Definition OrarFunctor_diag (F: OrarFunctor) (A: ofeT) : oraT := orarFunctor_car F A A.
Coercion OrarFunctor_diag : OrarFunctor >-> Funclass.

Program Definition OraconstRF (B : oraT) : OrarFunctor :=
  {| orarFunctor_car A1 A2 := B; orarFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion OraconstRF : oraT >-> OrarFunctor.

Instance OraconstRF_contractive B : OrarFunctorContractive (OraconstRF B).
Proof. rewrite /OrarFunctorContractive; apply _. Qed.

Structure uorarFunctor := UOraRFunctor {
  uorarFunctor_car : ofeT → ofeT → uoraT;
  uorarFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → uorarFunctor_car A1 B1 -n> uorarFunctor_car A2 B2;
  uorarFunctor_ne A1 A2 B1 B2 :
    NonExpansive (@uorarFunctor_map A1 A2 B1 B2);
  uorarFunctor_id {A B} (x : uorarFunctor_car A B) : uorarFunctor_map (cid,cid) x ≡ x;
  uorarFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    uorarFunctor_map (f◎g, g'◎f') x ≡ uorarFunctor_map (g,g') (uorarFunctor_map (f,f') x);
  uorarFunctor_mor {A1 A2 B1 B2} (fg : (A2 -n> A1) * (B1 -n> B2)) :
    OraMorphism (uorarFunctor_map fg)
}.
Existing Instances uorarFunctor_ne uorarFunctor_mor.
Instance: Params (@uorarFunctor_map) 5.

Delimit Scope uorarFunctor_scope with URF.
Bind Scope uorarFunctor_scope with uorarFunctor.

Class uorarFunctorContractive (F : uorarFunctor) :=
  uorarFunctor_contractive A1 A2 B1 B2 :> Contractive (@uorarFunctor_map F A1 A2 B1 B2).

Definition uorarFunctor_diag (F: uorarFunctor) (A: ofeT) : uoraT := uorarFunctor_car F A A.
Coercion uorarFunctor_diag : uorarFunctor >-> Funclass.

Program Definition OraconstURF (B : uoraT) : uorarFunctor :=
  {| uorarFunctor_car A1 A2 := B; uorarFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion OraconstURF : uoraT >-> uorarFunctor.

Instance OraconstURF_contractive B : uorarFunctorContractive (OraconstURF B).
Proof. rewrite /uorarFunctorContractive; apply _. Qed.

(** * Transporting a CMRA equality *)
Definition ora_transport {A B : oraT} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Section ora_transport.
  Context {A B : oraT} (H : A = B).
  Notation T := (ora_transport H).
  Global Instance ora_transport_ne : NonExpansive T.
  Proof. by intros ???; destruct H. Qed.
  Global Instance ora_transport_proper : Proper ((≡) ==> (≡)) T.
  Proof. by intros ???; destruct H. Qed.
  Lemma ora_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof. by destruct H. Qed.
  Lemma ora_transport_core x : T (core x) = core (T x).
  Proof. by destruct H. Qed.
  Lemma ora_transport_validN n x : ✓{n} T x ↔ ✓{n} x.
  Proof. by destruct H. Qed.
  Lemma ora_transport_valid x : ✓ T x ↔ ✓ x.
  Proof. by destruct H. Qed.
  Global Instance ora_transport_discrete x : Discrete x → Discrete (T x).
  Proof. by destruct H. Qed.
  Global Instance ora_transport_core_id x : OraCoreId x → OraCoreId (T x).
  Proof. by destruct H. Qed.
End ora_transport.

(* (** * Instances *) *)
(* (** ** Discrete CMRA *) *)
(* Record RAMixin A `{Equiv A, PCore A, Op A, Valid A} := { *)
(*   (* setoids *) *)
(*   ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x); *)
(*   ra_core_proper x y cx : *)
(*     x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy; *)
(*   ra_validN_proper : Proper ((≡) ==> impl) valid; *)
(*   (* monoid *) *)
(*   ra_assoc : Assoc (≡) (⋅); *)
(*   ra_comm : Comm (≡) (⋅); *)
(*   ra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x; *)
(*   ra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx; *)
(*   ra_pcore_mono x y cx : *)
(*     x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy; *)
(*   ra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x *)
(* }. *)

(* Section discrete. *)
(*   Local Set Default Proof Using "Type*". *)
(*   Context `{Equiv A, PCore A, Op A, Valid A} (Heq : @Equivalence A (≡)). *)
(*   Context (ra_mix : RAMixin A). *)
(*   Existing Instances discrete_dist. *)

(*   Instance discrete_validN : ValidN A := λ n x, ✓ x. *)
(*   Definition discrete_cmra_mixin : CmraMixin A. *)
(*   Proof. *)
(*     destruct ra_mix; split; try done. *)
(*     - intros x; split; first done. by move=> /(_ 0). *)
(*     - intros n x y1 y2 ??; by exists y1, y2. *)
(*   Qed. *)

(*   Instance discrete_cmra_discrete : *)
(*     CmraDiscrete (CmraT' A (discrete_ofe_mixin Heq) discrete_cmra_mixin A). *)
(*   Proof. split. apply _. done. Qed. *)
(* End discrete. *)

(* (** A smart constructor for the discrete RA over a carrier [A]. It uses *)
(* [ofe_discrete_equivalence_of A] to make sure the same [Equivalence] proof is *)
(* used as when constructing the OFE. *) *)
(* Notation discreteR A ra_mix := *)
(*   (CmraT A (discrete_cmra_mixin (discrete_ofe_equivalence_of A%type) ra_mix)) *)
(*   (only parsing). *)

(* Section ra_total. *)
(*   Local Set Default Proof Using "Type*". *)
(*   Context A `{Equiv A, PCore A, Op A, Valid A}. *)
(*   Context (total : ∀ x : A, is_Some (pcore x)). *)
(*   Context (op_proper : ∀ x : A, Proper ((≡) ==> (≡)) (op x)). *)
(*   Context (core_proper: Proper ((≡) ==> (≡)) (@core A _)). *)
(*   Context (valid_proper : Proper ((≡) ==> impl) (@valid A _)). *)
(*   Context (op_assoc : Assoc (≡) (@op A _)). *)
(*   Context (op_comm : Comm (≡) (@op A _)). *)
(*   Context (core_l : ∀ x : A, core x ⋅ x ≡ x). *)
(*   Context (core_idemp : ∀ x : A, core (core x) ≡ core x). *)
(*   Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y). *)
(*   Context (valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x). *)
(*   Lemma ra_total_mixin : RAMixin A. *)
(*   Proof. *)
(*     split; auto. *)
(*     - intros x y ? Hcx%core_proper Hx; move: Hcx. rewrite /core /= Hx /=. *)
(*       case (total y)=> [cy ->]; eauto. *)
(*     - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx. *)
(*     - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=. *)
(*       case (total cx)=>[ccx ->]; by constructor. *)
(*     - intros x y cx Hxy%core_mono Hx. move: Hxy. *)
(*       rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto. *)
(*   Qed. *)
(* End ra_total. *)

(* (** ** CMRA for the unit type *) *)
(* Section unit. *)
(*   Instance unit_valid : Valid () := λ x, True. *)
(*   Instance unit_validN : ValidN () := λ n x, True. *)
(*   Instance unit_pcore : PCore () := λ x, Some x. *)
(*   Instance unit_op : Op () := λ x y, (). *)
(*   Lemma unit_cmra_mixin : CmraMixin (). *)
(*   Proof. apply discrete_cmra_mixin, ra_total_mixin; by eauto. Qed. *)
(*   Canonical Structure unitR : cmraT := CmraT unit unit_cmra_mixin. *)

(*   Instance unit_unit : Unit () := (). *)
(*   Lemma unit_ucmra_mixin : UcmraMixin (). *)
(*   Proof. done. Qed. *)
(*   Canonical Structure unitUR : ucmraT := UcmraT unit unit_ucmra_mixin. *)

(*   Global Instance unit_cmra_discrete : CmraDiscrete unitR. *)
(*   Proof. done. Qed. *)
(*   Global Instance unit_core_id (x : ()) : CoreId x. *)
(*   Proof. by constructor. Qed. *)
(*   Global Instance unit_cancelable (x : ()) : Cancelable x. *)
(*   Proof. by constructor. Qed. *)
(* End unit. *)

(* (** ** Natural numbers *) *)
(* Section nat. *)
(*   Instance nat_valid : Valid nat := λ x, True. *)
(*   Instance nat_validN : ValidN nat := λ n x, True. *)
(*   Instance nat_pcore : PCore nat := λ x, Some 0. *)
(*   Instance nat_op : Op nat := plus. *)
(*   Definition nat_op_plus x y : x ⋅ y = x + y := eq_refl. *)
(*   Lemma nat_included (x y : nat) : x ≼ y ↔ x ≤ y. *)
(*   Proof. by rewrite nat_le_sum. Qed. *)
(*   Lemma nat_ra_mixin : RAMixin nat. *)
(*   Proof. *)
(*     apply ra_total_mixin; try by eauto. *)
(*     - solve_proper. *)
(*     - intros x y z. apply Nat.add_assoc. *)
(*     - intros x y. apply Nat.add_comm. *)
(*     - by exists 0. *)
(*   Qed. *)
(*   Canonical Structure natR : cmraT := discreteR nat nat_ra_mixin. *)

(*   Global Instance nat_cmra_discrete : CmraDiscrete natR. *)
(*   Proof. apply discrete_cmra_discrete. Qed. *)

(*   Instance nat_unit : Unit nat := 0. *)
(*   Lemma nat_ucmra_mixin : UcmraMixin nat. *)
(*   Proof. split; apply _ || done. Qed. *)
(*   Canonical Structure natUR : ucmraT := UcmraT nat nat_ucmra_mixin. *)

(*   Global Instance nat_cancelable (x : nat) : Cancelable x. *)
(*   Proof. by intros ???? ?%Nat.add_cancel_l. Qed. *)
(* End nat. *)

(* Definition mnat := nat. *)

(* Section mnat. *)
(*   Instance mnat_unit : Unit mnat := 0. *)
(*   Instance mnat_valid : Valid mnat := λ x, True. *)
(*   Instance mnat_validN : ValidN mnat := λ n x, True. *)
(*   Instance mnat_pcore : PCore mnat := Some. *)
(*   Instance mnat_op : Op mnat := Nat.max. *)
(*   Definition mnat_op_max x y : x ⋅ y = x `max` y := eq_refl. *)
(*   Lemma mnat_included (x y : mnat) : x ≼ y ↔ x ≤ y. *)
(*   Proof. *)
(*     split. *)
(*     - intros [z ->]; unfold op, mnat_op; lia. *)
(*     - exists y. by symmetry; apply Nat.max_r. *)
(*   Qed. *)
(*   Lemma mnat_ra_mixin : RAMixin mnat. *)
(*   Proof. *)
(*     apply ra_total_mixin; try by eauto. *)
(*     - solve_proper. *)
(*     - solve_proper. *)
(*     - intros x y z. apply Nat.max_assoc. *)
(*     - intros x y. apply Nat.max_comm. *)
(*     - intros x. apply Max.max_idempotent. *)
(*   Qed. *)
(*   Canonical Structure mnatR : cmraT := discreteR mnat mnat_ra_mixin. *)

(*   Global Instance mnat_cmra_discrete : CmraDiscrete mnatR. *)
(*   Proof. apply discrete_cmra_discrete. Qed. *)

(*   Lemma mnat_ucmra_mixin : UcmraMixin mnat. *)
(*   Proof. split; apply _ || done. Qed. *)
(*   Canonical Structure mnatUR : ucmraT := UcmraT mnat mnat_ucmra_mixin. *)

(*   Global Instance mnat_core_id (x : mnat) : CoreId x. *)
(*   Proof. by constructor. Qed. *)
(* End mnat. *)

(* (** ** Positive integers. *) *)
(* Section positive. *)
(*   Instance pos_valid : Valid positive := λ x, True. *)
(*   Instance pos_validN : ValidN positive := λ n x, True. *)
(*   Instance pos_pcore : PCore positive := λ x, None. *)
(*   Instance pos_op : Op positive := Pos.add. *)
(*   Definition pos_op_plus x y : x ⋅ y = (x + y)%positive := eq_refl. *)
(*   Lemma pos_included (x y : positive) : x ≼ y ↔ (x < y)%positive. *)
(*   Proof. by rewrite Plt_sum. Qed. *)
(*   Lemma pos_ra_mixin : RAMixin positive. *)
(*   Proof. *)
(*     split; try by eauto. *)
(*     - by intros ??? ->. *)
(*     - intros ???. apply Pos.add_assoc. *)
(*     - intros ??. apply Pos.add_comm. *)
(*   Qed. *)
(*   Canonical Structure positiveR : cmraT := discreteR positive pos_ra_mixin. *)

(*   Global Instance pos_cmra_discrete : CmraDiscrete positiveR. *)
(*   Proof. apply discrete_cmra_discrete. Qed. *)

(*   Global Instance pos_cancelable (x : positive) : Cancelable x. *)
(*   Proof. intros n y z ??. by eapply Pos.add_reg_l, leibniz_equiv. Qed. *)
(*   Global Instance pos_id_free (x : positive) : IdFree x. *)
(*   Proof. *)
(*     intros y ??. apply (Pos.add_no_neutral x y). rewrite Pos.add_comm. *)
(*     by apply leibniz_equiv. *)
(*   Qed. *)
(* End positive. *)

(** ** Product *)
(* Section prod. *)
(*   Context {A B : oraT}. *)
(*   Local Arguments pcore _ _ !_ /. *)
(*   Local Arguments ora_pcore _ !_/. *)

(*   Instance prod_op : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2). *)
(*   Instance prod_pcore : PCore (A * B) := λ x, *)
(*     c1 ← pcore (x.1); c2 ← pcore (x.2); Some (c1, c2). *)
(*   Arguments prod_pcore !_ /. *)
(*   Instance prod_valid : Valid (A * B) := λ x, ✓ x.1 ∧ ✓ x.2. *)
(*   Instance prod_validN : ValidN (A * B) := λ n x, ✓{n} x.1 ∧ ✓{n} x.2. *)
(*   Instance prod_order : OraOrder (A * B) := λ x y, x.1 ≼ₒ y.1 ∧ x.2 ≼ₒ y.2. *)
(*   Instance prod_orderN : OraOrderN (A * B) := λ n x y, x.1 ≼ₒ{n} y.1 ∧ x.2 ≼ₒ{n} y.2. *)

(*   Lemma prod_pcore_Some (x cx : A * B) : *)
(*     pcore x = Some cx ↔ pcore (x.1) = Some (cx.1) ∧ pcore (x.2) = Some (cx.2). *)
(*   Proof. destruct x, cx; by intuition simplify_option_eq. Qed. *)
(*   Lemma prod_pcore_Some' (x cx : A * B) : *)
(*     pcore x ≡ Some cx ↔ pcore (x.1) ≡ Some (cx.1) ∧ pcore (x.2) ≡ Some (cx.2). *)
(*   Proof. *)
(*     split; [by intros (cx'&[-> ->]%prod_pcore_Some&->)%equiv_Some_inv_r'|]. *)
(*     rewrite {3}/pcore /prod_pcore. (* TODO: use setoid rewrite *) *)
(*     intros [Hx1 Hx2]; inversion_clear Hx1; simpl; inversion_clear Hx2. *)
(*     by constructor. *)
(*   Qed. *)

(*   Lemma prod_included (x y : A * B) : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2. *)
(*   Proof. *)
(*     split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|]. *)
(*     intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto. *)
(*   Qed. *)
(*   Lemma prod_includedN (x y : A * B) n : x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2. *)
(*   Proof. *)
(*     split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|]. *)
(*     intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto. *)
(*   Qed. *)

(*   Definition prod_cmra_mixin : OraMixin (A * B). *)
(*   Proof. *)
(*     split; try apply _. *)
(*     - by intros n x y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2. *)
(*     - intros n x y cx; setoid_rewrite prod_pcore_Some=> -[??] [??]. *)
(*       destruct (ora_pcore_ne n (x.1) (y.1) (cx.1)) as (z1&->&?); auto. *)
(*       destruct (ora_pcore_ne n (x.2) (y.2) (cx.2)) as (z2&->&?); auto. *)
(*       exists (z1,z2); repeat constructor; auto. *)
(*     - by intros n y1 y2 [Hy1 Hy2] [??]; split; rewrite /= -?Hy1 -?Hy2. *)
(*     - intros x; split. *)
(*       + intros [??] n; split; by apply ora_valid_validN. *)
(*       + intros Hxy; split; apply ora_valid_validN=> n; apply Hxy. *)
(*     - by intros n x [??]; split; apply ora_validN_S. *)
(*     - by split; rewrite /= assoc. *)
(*     - by split; rewrite /= comm. *)
(*     - intros x y [??]%prod_pcore_Some; *)
(*         constructor; simpl; eauto using ora_pcore_l. *)
(*     - intros x y; rewrite prod_pcore_Some prod_pcore_Some'. *)
(*       naive_solver eauto using ora_pcore_idemp. *)
(*     - intros x y cx; rewrite prod_included prod_pcore_Some=> -[??] [??]. *)
(*       destruct (ora_pcore_monoN (x.1) (y.1) (cx.1)) as (z1&?&?); auto. *)
(*       destruct (cmra_pcore_mono (x.2) (y.2) (cx.2)) as (z2&?&?); auto. *)
(*       exists (z1,z2). by rewrite prod_included prod_pcore_Some. *)
(*     - intros n x y [??]; split; simpl in *; eauto using cmra_validN_op_l. *)
(*     - intros n x y1 y2 [??] [??]; simpl in *. *)
(*       destruct (cmra_extend n (x.1) (y1.1) (y2.1)) as (z11&z12&?&?&?); auto. *)
(*       destruct (cmra_extend n (x.2) (y1.2) (y2.2)) as (z21&z22&?&?&?); auto. *)
(*       by exists (z11,z21), (z12,z22). *)
(*   Qed. *)
(*   Canonical Structure prodR := CmraT (prod A B) prod_cmra_mixin. *)

(*   Lemma pair_op (a a' : A) (b b' : B) : (a, b) ⋅ (a', b') = (a ⋅ a', b ⋅ b'). *)
(*   Proof. done. Qed. *)

(*   Global Instance prod_cmra_total : CmraTotal A → CmraTotal B → CmraTotal prodR. *)
(*   Proof. *)
(*     intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?]. *)
(*     exists (ca,cb); by simplify_option_eq. *)
(*   Qed. *)

(*   Global Instance prod_cmra_discrete : *)
(*     CmraDiscrete A → CmraDiscrete B → CmraDiscrete prodR. *)
(*   Proof. split. apply _. by intros ? []; split; apply cmra_discrete_valid. Qed. *)

(*   Global Instance pair_core_id x y : *)
(*     CoreId x → CoreId y → CoreId (x,y). *)
(*   Proof. by rewrite /CoreId prod_pcore_Some'. Qed. *)

(*   Global Instance pair_exclusive_l x y : Exclusive x → Exclusive (x,y). *)
(*   Proof. by intros ?[][?%exclusive0_l]. Qed. *)
(*   Global Instance pair_exclusive_r x y : Exclusive y → Exclusive (x,y). *)
(*   Proof. by intros ?[][??%exclusive0_l]. Qed. *)

(*   Global Instance pair_cancelable x y : *)
(*     Cancelable x → Cancelable y → Cancelable (x,y). *)
(*   Proof. intros ???[][][][]. constructor; simpl in *; by eapply cancelableN. Qed. *)

(*   Global Instance pair_id_free_l x y : IdFree x → IdFree (x,y). *)
(*   Proof. move=>? [??] [? _] [/=? _]. eauto. Qed. *)
(*   Global Instance pair_id_free_r x y : IdFree y → IdFree (x,y). *)
(*   Proof. move=>? [??] [_ ?] [_ /=?]. eauto. Qed. *)
(* End prod. *)

(* Arguments prodR : clear implicits. *)

(* Section prod_unit. *)
(*   Context {A B : ucmraT}. *)

(*   Instance prod_unit `{Unit A, Unit B} : Unit (A * B) := (ε, ε). *)
(*   Lemma prod_ucmra_mixin : UcmraMixin (A * B). *)
(*   Proof. *)
(*     split. *)
(*     - split; apply ucmra_unit_valid. *)
(*     - by split; rewrite /=left_id. *)
(*     - rewrite prod_pcore_Some'; split; apply (core_id _). *)
(*   Qed. *)
(*   Canonical Structure prodUR := UcmraT (prod A B) prod_ucmra_mixin. *)

(*   Lemma pair_split (x : A) (y : B) : (x, y) ≡ (x, ε) ⋅ (ε, y). *)
(*   Proof. by rewrite pair_op left_id right_id. Qed. *)

(*   Lemma pair_split_L `{!LeibnizEquiv A, !LeibnizEquiv B} (x : A) (y : B) : *)
(*     (x, y) = (x, ε) ⋅ (ε, y). *)
(*   Proof. unfold_leibniz. apply pair_split. Qed. *)
(* End prod_unit. *)

(* Arguments prodUR : clear implicits. *)

(* Instance prod_map_cmra_morphism {A A' B B' : cmraT} (f : A → A') (g : B → B') : *)
(*   CmraMorphism f → CmraMorphism g → CmraMorphism (prod_map f g). *)
(* Proof. *)
(*   split; first apply _. *)
(*   - by intros n x [??]; split; simpl; apply cmra_morphism_validN. *)
(*   - intros x. etrans. apply (reflexivity (mbind _ _)). *)
(*     etrans; last apply (reflexivity (_ <$> mbind _ _)). simpl. *)
(*     assert (Hf := cmra_morphism_pcore f (x.1)). *)
(*     destruct (pcore (f (x.1))), (pcore (x.1)); inversion_clear Hf=>//=. *)
(*     assert (Hg := cmra_morphism_pcore g (x.2)). *)
(*     destruct (pcore (g (x.2))), (pcore (x.2)); inversion_clear Hg=>//=. *)
(*     by setoid_subst. *)
(*   - intros. by rewrite /prod_map /= -!cmra_morphism_op. *)
(* Qed. *)

(* Program Definition prodRF (F1 F2 : rFunctor) : rFunctor := {| *)
(*   rFunctor_car A B := prodR (rFunctor_car F1 A B) (rFunctor_car F2 A B); *)
(*   rFunctor_map A1 A2 B1 B2 fg := *)
(*     prodC_map (rFunctor_map F1 fg) (rFunctor_map F2 fg) *)
(* |}. *)
(* Next Obligation. *)
(*   intros F1 F2 A1 A2 B1 B2 n ???. by apply prodC_map_ne; apply rFunctor_ne. *)
(* Qed. *)
(* Next Obligation. by intros F1 F2 A B [??]; rewrite /= !rFunctor_id. Qed. *)
(* Next Obligation. *)
(*   intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl. *)
(*   by rewrite !rFunctor_compose. *)
(* Qed. *)
(* Notation "F1 * F2" := (prodRF F1%RF F2%RF) : rFunctor_scope. *)

(* Instance prodRF_contractive F1 F2 : *)
(*   rFunctorContractive F1 → rFunctorContractive F2 → *)
(*   rFunctorContractive (prodRF F1 F2). *)
(* Proof. *)
(*   intros ?? A1 A2 B1 B2 n ???; *)
(*     by apply prodC_map_ne; apply rFunctor_contractive. *)
(* Qed. *)

(* Program Definition prodURF (F1 F2 : urFunctor) : urFunctor := {| *)
(*   urFunctor_car A B := prodUR (urFunctor_car F1 A B) (urFunctor_car F2 A B); *)
(*   urFunctor_map A1 A2 B1 B2 fg := *)
(*     prodC_map (urFunctor_map F1 fg) (urFunctor_map F2 fg) *)
(* |}. *)
(* Next Obligation. *)
(*   intros F1 F2 A1 A2 B1 B2 n ???. by apply prodC_map_ne; apply urFunctor_ne. *)
(* Qed. *)
(* Next Obligation. by intros F1 F2 A B [??]; rewrite /= !urFunctor_id. Qed. *)
(* Next Obligation. *)
(*   intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl. *)
(*   by rewrite !urFunctor_compose. *)
(* Qed. *)
(* Notation "F1 * F2" := (prodURF F1%URF F2%URF) : urFunctor_scope. *)

(* Instance prodURF_contractive F1 F2 : *)
(*   urFunctorContractive F1 → urFunctorContractive F2 → *)
(*   urFunctorContractive (prodURF F1 F2). *)
(* Proof. *)
(*   intros ?? A1 A2 B1 B2 n ???; *)
(*     by apply prodC_map_ne; apply urFunctor_contractive. *)
(* Qed. *)

(* (** ** CMRA for the option type *) *)
(* Section option. *)
(*   Context {A : cmraT}. *)
(*   Implicit Types a b : A. *)
(*   Implicit Types ma mb : option A. *)
(*   Local Arguments core _ _ !_ /. *)
(*   Local Arguments pcore _ _ !_ /. *)

(*   Instance option_valid : Valid (option A) := λ ma, *)
(*     match ma with Some a => ✓ a | None => True end. *)
(*   Instance option_validN : ValidN (option A) := λ n ma, *)
(*     match ma with Some a => ✓{n} a | None => True end. *)
(*   Instance option_pcore : PCore (option A) := λ ma, Some (ma ≫= pcore). *)
(*   Arguments option_pcore !_ /. *)
(*   Instance option_op : Op (option A) := union_with (λ a b, Some (a ⋅ b)). *)

(*   Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _. *)
(*   Definition Some_validN a n : ✓{n} Some a ↔ ✓{n} a := reflexivity _. *)
(*   Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl. *)
(*   Lemma Some_core `{CmraTotal A} a : Some (core a) = core (Some a). *)
(*   Proof. rewrite /core /=. by destruct (cmra_total a) as [? ->]. Qed. *)
(*   Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma). *)
(*   Proof. by destruct ma. Qed. *)

(*   Lemma option_included ma mb : *)
(*     ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a ≡ b ∨ a ≼ b). *)
(*   Proof. *)
(*     split. *)
(*     - intros [mc Hmc]. *)
(*       destruct ma as [a|]; [right|by left]. *)
(*       destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc]. *)
(*       destruct mc as [c|]; inversion_clear Hmc; split_and?; auto; *)
(*         setoid_subst; eauto using cmra_included_l. *)
(*     - intros [->|(a&b&->&->&[Hc|[c Hc]])]. *)
(*       + exists mb. by destruct mb. *)
(*       + exists None; by constructor. *)
(*       + exists (Some c); by constructor. *)
(*   Qed. *)

(*   Lemma option_includedN n ma mb : *)
(*     ma ≼{n} mb ↔ ma = None ∨ ∃ x y, ma = Some x ∧ mb = Some y ∧ (x ≡{n}≡ y ∨ x ≼{n} y). *)
(*   Proof. *)
(*     split. *)
(*     - intros [mc Hmc]. *)
(*       destruct ma as [a|]; [right|by left]. *)
(*       destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc]. *)
(*       destruct mc as [c|]; inversion_clear Hmc; split_and?; auto; *)
(*         ofe_subst; eauto using cmra_includedN_l. *)
(*     - intros [->|(a&y&->&->&[Hc|[c Hc]])]. *)
(*       + exists mb. by destruct mb. *)
(*       + exists None; by constructor. *)
(*       + exists (Some c); by constructor. *)
(*   Qed. *)

(*   Lemma option_cmra_mixin : CmraMixin (option A). *)
(*   Proof. *)
(*     apply cmra_total_mixin. *)
(*     - eauto. *)
(*     - by intros [a|] n; destruct 1; constructor; ofe_subst. *)
(*     - destruct 1; by ofe_subst. *)
(*     - by destruct 1; rewrite /validN /option_validN //=; ofe_subst. *)
(*     - intros [a|]; [apply cmra_valid_validN|done]. *)
(*     - intros n [a|]; unfold validN, option_validN; eauto using cmra_validN_S. *)
(*     - intros [a|] [b|] [c|]; constructor; rewrite ?assoc; auto. *)
(*     - intros [a|] [b|]; constructor; rewrite 1?comm; auto. *)
(*     - intros [a|]; simpl; auto. *)
(*       destruct (pcore a) as [ca|] eqn:?; constructor; eauto using cmra_pcore_l. *)
(*     - intros [a|]; simpl; auto. *)
(*       destruct (pcore a) as [ca|] eqn:?; simpl; eauto using cmra_pcore_idemp. *)
(*     - intros ma mb; setoid_rewrite option_included. *)
(*       intros [->|(a&b&->&->&[?|?])]; simpl; eauto. *)
(*       + destruct (pcore a) as [ca|] eqn:?; eauto. *)
(*         destruct (cmra_pcore_proper a b ca) as (?&?&?); eauto 10. *)
(*       + destruct (pcore a) as [ca|] eqn:?; eauto. *)
(*         destruct (cmra_pcore_mono a b ca) as (?&?&?); eauto 10. *)
(*     - intros n [a|] [b|]; rewrite /validN /option_validN /=; *)
(*         eauto using cmra_validN_op_l. *)
(*     - intros n ma mb1 mb2. *)
(*       destruct ma as [a|], mb1 as [b1|], mb2 as [b2|]; intros Hx Hx'; *)
(*         inversion_clear Hx'; auto. *)
(*       + destruct (cmra_extend n a b1 b2) as (c1&c2&?&?&?); auto. *)
(*         by exists (Some c1), (Some c2); repeat constructor. *)
(*       + by exists (Some a), None; repeat constructor. *)
(*       + by exists None, (Some a); repeat constructor. *)
(*       + exists None, None; repeat constructor. *)
(*   Qed. *)
(*   Canonical Structure optionR := CmraT (option A) option_cmra_mixin. *)

(*   Global Instance option_cmra_discrete : CmraDiscrete A → CmraDiscrete optionR. *)
(*   Proof. split; [apply _|]. by intros [a|]; [apply (cmra_discrete_valid a)|]. Qed. *)

(*   Instance option_unit : Unit (option A) := None. *)
(*   Lemma option_ucmra_mixin : UcmraMixin optionR. *)
(*   Proof. split. done. by intros []. done. Qed. *)
(*   Canonical Structure optionUR := UcmraT (option A) option_ucmra_mixin. *)

(*   (** Misc *) *)
(*   Lemma op_None ma mb : ma ⋅ mb = None ↔ ma = None ∧ mb = None. *)
(*   Proof. destruct ma, mb; naive_solver. Qed. *)
(*   Lemma op_is_Some ma mb : is_Some (ma ⋅ mb) ↔ is_Some ma ∨ is_Some mb. *)
(*   Proof. rewrite -!not_eq_None_Some op_None. destruct ma, mb; naive_solver. Qed. *)

(*   Lemma cmra_opM_assoc' a mb mc : a ⋅? mb ⋅? mc ≡ a ⋅? (mb ⋅ mc). *)
(*   Proof. destruct mb, mc; by rewrite /= -?assoc. Qed. *)

(*   Global Instance Some_core_id a : CoreId a → CoreId (Some a). *)
(*   Proof. by constructor. Qed. *)
(*   Global Instance option_core_id ma : (∀ x : A, CoreId x) → CoreId ma. *)
(*   Proof. intros. destruct ma; apply _. Qed. *)

(*   Lemma exclusiveN_Some_l n a `{!Exclusive a} mb : *)
(*     ✓{n} (Some a ⋅ mb) → mb = None. *)
(*   Proof. destruct mb. move=> /(exclusiveN_l _ a) []. done. Qed. *)
(*   Lemma exclusiveN_Some_r n a `{!Exclusive a} mb : *)
(*     ✓{n} (mb ⋅ Some a) → mb = None. *)
(*   Proof. rewrite comm. by apply exclusiveN_Some_l. Qed. *)

(*   Lemma exclusive_Some_l a `{!Exclusive a} mb : ✓ (Some a ⋅ mb) → mb = None. *)
(*   Proof. destruct mb. move=> /(exclusive_l a) []. done. Qed. *)
(*   Lemma exclusive_Some_r a `{!Exclusive a} mb : ✓ (mb ⋅ Some a) → mb = None. *)
(*   Proof. rewrite comm. by apply exclusive_Some_l. Qed. *)

(*   Lemma Some_includedN n a b : Some a ≼{n} Some b ↔ a ≡{n}≡ b ∨ a ≼{n} b. *)
(*   Proof. rewrite option_includedN; naive_solver. Qed. *)
(*   Lemma Some_included a b : Some a ≼ Some b ↔ a ≡ b ∨ a ≼ b. *)
(*   Proof. rewrite option_included; naive_solver. Qed. *)
(*   Lemma Some_included_2 a b : a ≼ b → Some a ≼ Some b. *)
(*   Proof. rewrite Some_included; eauto. Qed. *)

(*   Lemma Some_includedN_total `{CmraTotal A} n a b : Some a ≼{n} Some b ↔ a ≼{n} b. *)
(*   Proof. rewrite Some_includedN. split. by intros [->|?]. eauto. Qed. *)
(*   Lemma Some_included_total `{CmraTotal A} a b : Some a ≼ Some b ↔ a ≼ b. *)
(*   Proof. rewrite Some_included. split. by intros [->|?]. eauto. Qed. *)

(*   Lemma Some_includedN_exclusive n a `{!Exclusive a} b : *)
(*     Some a ≼{n} Some b → ✓{n} b → a ≡{n}≡ b. *)
(*   Proof. move=> /Some_includedN [//|/exclusive_includedN]; tauto. Qed. *)
(*   Lemma Some_included_exclusive a `{!Exclusive a} b : *)
(*     Some a ≼ Some b → ✓ b → a ≡ b. *)
(*   Proof. move=> /Some_included [//|/exclusive_included]; tauto. Qed. *)

(*   Lemma is_Some_includedN n ma mb : ma ≼{n} mb → is_Some ma → is_Some mb. *)
(*   Proof. rewrite -!not_eq_None_Some option_includedN. naive_solver. Qed. *)
(*   Lemma is_Some_included ma mb : ma ≼ mb → is_Some ma → is_Some mb. *)
(*   Proof. rewrite -!not_eq_None_Some option_included. naive_solver. Qed. *)

(*   Global Instance cancelable_Some a : *)
(*     IdFree a → Cancelable a → Cancelable (Some a). *)
(*   Proof. *)
(*     intros Hirr ?? [b|] [c|] ? EQ; inversion_clear EQ. *)
(*     - constructor. by apply (cancelableN a). *)
(*     - destruct (Hirr b); [|eauto using dist_le with lia]. *)
(*       by eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n); last lia. *)
(*     - destruct (Hirr c); [|symmetry; eauto using dist_le with lia]. *)
(*       by eapply (cmra_validN_le n); last lia. *)
(*     - done. *)
(*   Qed. *)
(* End option. *)

(* Arguments optionR : clear implicits. *)
(* Arguments optionUR : clear implicits. *)

(* Section option_prod. *)
(*   Context {A B : cmraT}. *)
(*   Implicit Types a : A. *)
(*   Implicit Types b : B. *)

(*   Lemma Some_pair_includedN n a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ Some b1 ≼{n} Some b2. *)
(*   Proof. rewrite !Some_includedN. intros [[??]|[??]%prod_includedN]; eauto. Qed. *)
(*   Lemma Some_pair_includedN_total_1 `{CmraTotal A} n a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼{n} Some (a2,b2) → a1 ≼{n} a2 ∧ Some b1 ≼{n} Some b2. *)
(*   Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ a1). Qed. *)
(*   Lemma Some_pair_includedN_total_2 `{CmraTotal B} n a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ b1 ≼{n} b2. *)
(*   Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ b1). Qed. *)

(*   Lemma Some_pair_included a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ Some b1 ≼ Some b2. *)
(*   Proof. rewrite !Some_included. intros [[??]|[??]%prod_included]; eauto. Qed. *)
(*   Lemma Some_pair_included_total_1 `{CmraTotal A} a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼ Some (a2,b2) → a1 ≼ a2 ∧ Some b1 ≼ Some b2. *)
(*   Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total a1). Qed. *)
(*   Lemma Some_pair_included_total_2 `{CmraTotal B} a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ b1 ≼ b2. *)
(*   Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total b1). Qed. *)
(* End option_prod. *)

(* Instance option_fmap_cmra_morphism {A B : cmraT} (f: A → B) `{!CmraMorphism f} : *)
(*   CmraMorphism (fmap f : option A → option B). *)
(* Proof. *)
(*   split; first apply _. *)
(*   - intros n [a|] ?; rewrite /cmra_validN //=. by apply (cmra_morphism_validN f). *)
(*   - move=> [a|] //. by apply Some_proper, cmra_morphism_pcore. *)
(*   - move=> [a|] [b|] //=. by rewrite -(cmra_morphism_op f). *)
(* Qed. *)

(* Program Definition optionRF (F : rFunctor) : rFunctor := {| *)
(*   rFunctor_car A B := optionR (rFunctor_car F A B); *)
(*   rFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg) *)
(* |}. *)
(* Next Obligation. *)
(*   by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_ne. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros F A B x. rewrite /= -{2}(option_fmap_id x). *)
(*   apply option_fmap_equiv_ext=>y; apply rFunctor_id. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose. *)
(*   apply option_fmap_equiv_ext=>y; apply rFunctor_compose. *)
(* Qed. *)

(* Instance optionRF_contractive F : *)
(*   rFunctorContractive F → rFunctorContractive (optionRF F). *)
(* Proof. *)
(*   by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive. *)
(* Qed. *)

(* Program Definition optionURF (F : rFunctor) : urFunctor := {| *)
(*   urFunctor_car A B := optionUR (rFunctor_car F A B); *)
(*   urFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg) *)
(* |}. *)
(* Next Obligation. *)
(*   by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_ne. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros F A B x. rewrite /= -{2}(option_fmap_id x). *)
(*   apply option_fmap_equiv_ext=>y; apply rFunctor_id. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose. *)
(*   apply option_fmap_equiv_ext=>y; apply rFunctor_compose. *)
(* Qed. *)

(* Instance optionURF_contractive F : *)
(*   rFunctorContractive F → urFunctorContractive (optionURF F). *)
(* Proof. *)
(*   by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive. *)
(* Qed. *)

(* (* Dependently-typed functions over a finite discrete domain *) *)
(* Section ofe_fun_cmra. *)
(*   Context `{Hfin : Finite A} {B : A → ucmraT}. *)
(*   Implicit Types f g : ofe_fun B. *)

(*   Instance ofe_fun_op : Op (ofe_fun B) := λ f g x, f x ⋅ g x. *)
(*   Instance ofe_fun_pcore : PCore (ofe_fun B) := λ f, Some (λ x, core (f x)). *)
(*   Instance ofe_fun_valid : Valid (ofe_fun B) := λ f, ∀ x, ✓ f x. *)
(*   Instance ofe_fun_validN : ValidN (ofe_fun B) := λ n f, ∀ x, ✓{n} f x. *)

(*   Definition ofe_fun_lookup_op f g x : (f ⋅ g) x = f x ⋅ g x := eq_refl. *)
(*   Definition ofe_fun_lookup_core f x : (core f) x = core (f x) := eq_refl. *)

(*   Lemma ofe_fun_included_spec (f g : ofe_fun B) : f ≼ g ↔ ∀ x, f x ≼ g x. *)
(*   Proof using Hfin. *)
(*     split; [by intros [h Hh] x; exists (h x); rewrite /op /ofe_fun_op (Hh x)|]. *)
(*     intros [h ?]%finite_choice. by exists h. *)
(*   Qed. *)

(*   Lemma ofe_fun_cmra_mixin : CmraMixin (ofe_fun B). *)
(*   Proof using Hfin. *)
(*     apply cmra_total_mixin. *)
(*     - eauto. *)
(*     - by intros n f1 f2 f3 Hf x; rewrite ofe_fun_lookup_op (Hf x). *)
(*     - by intros n f1 f2 Hf x; rewrite ofe_fun_lookup_core (Hf x). *)
(*     - by intros n f1 f2 Hf ? x; rewrite -(Hf x). *)
(*     - intros g; split. *)
(*       + intros Hg n i; apply cmra_valid_validN, Hg. *)
(*       + intros Hg i; apply cmra_valid_validN=> n; apply Hg. *)
(*     - intros n f Hf x; apply cmra_validN_S, Hf. *)
(*     - by intros f1 f2 f3 x; rewrite ofe_fun_lookup_op assoc. *)
(*     - by intros f1 f2 x; rewrite ofe_fun_lookup_op comm. *)
(*     - by intros f x; rewrite ofe_fun_lookup_op ofe_fun_lookup_core cmra_core_l. *)
(*     - by intros f x; rewrite ofe_fun_lookup_core cmra_core_idemp. *)
(*     - intros f1 f2; rewrite !ofe_fun_included_spec=> Hf x. *)
(*       by rewrite ofe_fun_lookup_core; apply cmra_core_mono, Hf. *)
(*     - intros n f1 f2 Hf x; apply cmra_validN_op_l with (f2 x), Hf. *)
(*     - intros n f f1 f2 Hf Hf12. *)
(*       destruct (finite_choice (λ x (yy : B x * B x), *)
(*         f x ≡ yy.1 ⋅ yy.2 ∧ yy.1 ≡{n}≡ f1 x ∧ yy.2 ≡{n}≡ f2 x)) as [gg Hgg]. *)
(*       { intros x. specialize (Hf12 x). *)
(*         destruct (cmra_extend n (f x) (f1 x) (f2 x)) as (y1&y2&?&?&?); eauto. *)
(*         exists (y1,y2); eauto. } *)
(*       exists (λ x, (gg x).1), (λ x, (gg x).2). split_and!=> -?; naive_solver. *)
(*   Qed. *)
(*   Canonical Structure ofe_funR := CmraT (ofe_fun B) ofe_fun_cmra_mixin. *)

(*   Instance ofe_fun_unit : Unit (ofe_fun B) := λ x, ε. *)
(*   Definition ofe_fun_lookup_empty x : ε x = ε := eq_refl. *)

(*   Lemma ofe_fun_ucmra_mixin : UcmraMixin (ofe_fun B). *)
(*   Proof. *)
(*     split. *)
(*     - intros x; apply ucmra_unit_valid. *)
(*     - by intros f x; rewrite ofe_fun_lookup_op left_id. *)
(*     - constructor=> x. apply core_id_core, _. *)
(*   Qed. *)
(*   Canonical Structure ofe_funUR := UcmraT (ofe_fun B) ofe_fun_ucmra_mixin. *)

(*   Global Instance ofe_fun_unit_discrete : *)
(*     (∀ i, Discrete (ε : B i)) → Discrete (ε : ofe_fun B). *)
(*   Proof. intros ? f Hf x. by apply: discrete. Qed. *)
(* End ofe_fun_cmra. *)

(* Arguments ofe_funR {_ _ _} _. *)
(* Arguments ofe_funUR {_ _ _} _. *)

(* Instance ofe_fun_map_cmra_morphism *)
(*     `{Finite A} {B1 B2 : A → ucmraT} (f : ∀ x, B1 x → B2 x) : *)
(*   (∀ x, CmraMorphism (f x)) → CmraMorphism (ofe_fun_map f). *)
(* Proof. *)
(*   split; first apply _. *)
(*   - intros n g Hg x; rewrite /ofe_fun_map; apply (cmra_morphism_validN (f _)), Hg. *)
(*   - intros. apply Some_proper=>i. apply (cmra_morphism_core (f i)). *)
(*   - intros g1 g2 i. by rewrite /ofe_fun_map ofe_fun_lookup_op cmra_morphism_op. *)
(* Qed. *)

(* Program Definition ofe_funURF `{Finite C} (F : C → urFunctor) : urFunctor := {| *)
(*   urFunctor_car A B := ofe_funUR (λ c, urFunctor_car (F c) A B); *)
(*   urFunctor_map A1 A2 B1 B2 fg := ofe_funC_map (λ c, urFunctor_map (F c) fg) *)
(* |}. *)
(* Next Obligation. *)
(*   intros C ?? F A1 A2 B1 B2 n ?? g. *)
(*   by apply ofe_funC_map_ne=>?; apply urFunctor_ne. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros C ?? F A B g; simpl. rewrite -{2}(ofe_fun_map_id g). *)
(*   apply ofe_fun_map_ext=> y; apply urFunctor_id. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros C ?? F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g. rewrite /=-ofe_fun_map_compose. *)
(*   apply ofe_fun_map_ext=>y; apply urFunctor_compose. *)
(* Qed. *)
(* Instance ofe_funURF_contractive `{Finite C} (F : C → urFunctor) : *)
(*   (∀ c, urFunctorContractive (F c)) → urFunctorContractive (ofe_funURF F). *)
(* Proof. *)
(*   intros ? A1 A2 B1 B2 n ?? g. *)
(*   by apply ofe_funC_map_ne=>c; apply urFunctor_contractive. *)
(* Qed. *)
