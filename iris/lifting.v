Require Export iris.weakestpre.
Require Import iris.wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => solve_elem_of.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with H : wsat _ _ _ _ |- _ => apply wsat_valid in H end;
  solve_validN.

Section lifting.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types Q : val Λ → iProp Λ Σ.
Transparent uPred_holds.

Lemma wp_lift_step E1 E2
    (φ : expr Λ → state Λ → option (expr Λ) → Prop) Q e1 σ1 :
  E1 ⊆ E2 → to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  pvs E2 E1 (ownP σ1 ★ ▷ ∀ e2 σ2 ef, (■ φ e2 σ2 ef ∧ ownP σ2) -★
    pvs E1 E2 (wp E2 e2 Q ★ default True ef (flip (wp coPset_all) (λ _, True))))
  ⊑ wp E2 e1 Q.
Proof.
  intros ? He Hsafe Hstep r n ? Hvs; constructor; auto.
  intros rf k Ef σ1' ???; destruct (Hvs rf (S k) Ef σ1')
    as (r'&(r1&r2&?&?&Hwp)&Hws); auto; clear Hvs; cofe_subst r'.
  destruct (wsat_update_pst k (E1 ∪ Ef) σ1 σ1' r1 (r2 ⋅ rf)) as [-> Hws'].
  { by apply ownP_spec; auto. }
  { by rewrite (associative _). }
  constructor; [done|intros e2 σ2 ef ?; specialize (Hws' σ2)].
  destruct (λ H1 H2 H3, Hwp e2 σ2 ef (update_pst σ2 r1) k H1 H2 H3 rf k Ef σ2)
    as (r'&(r1'&r2'&?&?&?)&?); auto; cofe_subst r'.
  { split. destruct k; try eapply Hstep; eauto. apply ownP_spec; auto. }
  { rewrite (commutative _ r2) -(associative _); eauto using wsat_le. }
  by exists r1', r2'; split_ands; [| |by intros ? ->].
Qed.

Lemma wp_lift_pure_step E (φ : expr Λ → option (expr Λ) → Prop) Q e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (▷ ∀ e2 ef, ■ φ e2 ef →
    wp E e2 Q ★ default True ef (flip (wp coPset_all) (λ _, True)))
  ⊑ wp E e1 Q.
Proof.
  intros He Hsafe Hstep r [|n] ?; [done|]; intros Hwp; constructor; auto.
  intros rf k Ef σ1 ???; split; [done|].
  intros e2 σ2 ef ?; destruct (Hstep σ1 e2 σ2 ef); auto; subst.
  destruct (Hwp e2 ef r k) as (r1&r2&Hr&?&?); auto; [by destruct k|].
  exists r1,r2; split_ands; [rewrite -Hr| |by intros ? ->]; eauto using wsat_le.
Qed.

(** Derived lifting lemmas. *)
Opaque uPred_holds.
Import uPred.

Lemma wp_lift_atomic_step {E Q} e1 (φ : val Λ → state Λ → Prop) σ1 :
  to_val e1 = None →
  reducible e1 σ1 →
  (∀ e' σ' ef, prim_step e1 σ1 e' σ' ef → ∃ v', ef = None ∧ to_val e' = Some v' ∧ φ v' σ') →
  (ownP σ1 ★ ▷ ∀ v2 σ2, (■ φ v2 σ2 ∧ ownP σ2 -★ Q v2)) ⊑ wp E e1 Q.
Proof.
  intros He Hsafe Hstep.
  rewrite -(wp_lift_step E E
    (λ e' σ' ef, ∃ v', ef = None ∧ to_val e' = Some v' ∧ φ v' σ') _ e1 σ1) //; [].
  rewrite -pvs_intro. apply sep_mono, later_mono; first done.
  apply forall_intro=>e2'; apply forall_intro=>σ2'.
  apply forall_intro=>ef; apply wand_intro_l.
  rewrite always_and_sep_l' -associative -always_and_sep_l'.
  apply const_elim_l=>-[v2' [-> [Hv ?]]] /=.
  rewrite -pvs_intro right_id -wp_value'; last by eassumption.
  rewrite (forall_elim v2') (forall_elim σ2') const_equiv //.
  by rewrite left_id wand_elim_r.
Qed.

Lemma wp_lift_atomic_det_step {E Q e1} σ1 v2 σ2 :
  to_val e1 = None →
  reducible e1 σ1 →
  (∀ e' σ' ef, prim_step e1 σ1 e' σ' ef → ef = None ∧ e' = of_val v2 ∧ σ' = σ2) →
  (ownP σ1 ★ ▷ (ownP σ2 -★ Q v2)) ⊑ wp E e1 Q.
Proof.
  intros He Hsafe Hstep.
  rewrite -(wp_lift_atomic_step _ (λ v' σ', v' = v2 ∧ σ' = σ2) σ1) //; last first.
  { intros. exists v2. apply Hstep in H. destruct_conjs; subst.
    eauto using to_of_val. }
  apply sep_mono, later_mono; first done.
  apply forall_intro=>e2'; apply forall_intro=>σ2'.
  apply wand_intro_l.
  rewrite always_and_sep_l' -associative -always_and_sep_l'.
  apply const_elim_l=>-[-> ->] /=.
  by rewrite wand_elim_r.
Qed.

Lemma wp_lift_pure_det_step {E Q} e1 e2 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e' σ' ef, prim_step e1 σ1 e' σ' ef → σ1 = σ' ∧ ef = None ∧ e' = e2) →
  (▷ wp E e2 Q) ⊑ wp E e1 Q.
Proof.
  intros. rewrite -(wp_lift_pure_step E (λ e' ef, ef = None ∧ e' = e2) _ e1) //=.
  apply later_mono, forall_intro=>e'; apply forall_intro=>ef.
  apply impl_intro_l, const_elim_l=>-[-> ->] /=.
  by rewrite right_id.
Qed.

End lifting.
