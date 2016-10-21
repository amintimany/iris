From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth.
From iris.heap_lang Require Import proofmode notation.

Definition newcounter : val := λ: <>, ref #0.
Definition inc : val :=
  rec: "inc" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "inc" "l".
Definition read : val := λ: "l", !"l".
Global Opaque newcounter inc get.

(** Monotone counter *)
Class mcounterG Σ := MCounterG { mcounter_inG :> inG Σ (authR mnatUR) }.
Definition mcounterΣ : gFunctors := #[GFunctor (constRF (authR mnatUR))].

Instance subG_mcounterΣ {Σ} : subG mcounterΣ Σ → mcounterG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section mono_proof.
  Context `{!heapG Σ, !mcounterG Σ} (N : namespace).

  Definition mcounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (● (n : mnat)) ★ l ↦ #n)%I.

  Definition mcounter (l : loc) (n : nat) : iProp Σ :=
    (∃ γ, heapN ⊥ N ∧ heap_ctx ∧
          inv N (mcounter_inv γ l) ∧ own γ (◯ (n : mnat)))%I.

  (** The main proofs. *)
  Global Instance mcounter_persistent l n : PersistentP (mcounter l n).
  Proof. apply _. Qed.

  Lemma newcounter_mono_spec (R : iProp Σ) Φ :
    heapN ⊥ N →
    heap_ctx ★ (∀ l, mcounter l 0 -★ Φ #l) ⊢ WP newcounter #() {{ Φ }}.
  Proof.
    iIntros (?) "[#Hh HΦ]". rewrite /newcounter /=. wp_seq. wp_alloc l as "Hl".
    iUpd (own_alloc (● (O:mnat) ⋅ ◯ (O:mnat))) as (γ) "[Hγ Hγ']"; first done.
    iUpd (inv_alloc N _ (mcounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0%nat. by iFrame. }
    iUpdIntro. iApply "HΦ". rewrite /mcounter; eauto 10.
  Qed.

  Lemma inc_mono_spec l n (Φ : val → iProp Σ) :
    mcounter l n ★ (mcounter l (S n) -★ Φ #()) ⊢ WP inc #l {{ Φ }}.
  Proof.
    iIntros "[Hl HΦ]". iLöb as "IH". wp_rec.
    iDestruct "Hl" as (γ) "(% & #? & #Hinv & Hγf)".
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]" "Hclose".
    wp_load. iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    iUpdIntro. wp_let. wp_op.
    wp_bind (CAS _ _ _). iInv N as (c') ">[Hγ Hl]" "Hclose".
    destruct (decide (c' = c)) as [->|].
    - iDestruct (own_valid_2 with "[$Hγ $Hγf]")
        as %[?%mnat_included _]%auth_valid_discrete_2.
      iUpd (own_update_2 with "[$Hγ $Hγf]") as "[Hγ Hγf]".
      { apply auth_update, (mnat_local_update _ _ (S c)); auto. } 
      wp_cas_suc. iUpd ("Hclose" with "[Hl Hγ]") as "_".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      iUpdIntro. wp_if. iApply "HΦ"; iExists γ; repeat iSplit; eauto.
      iApply (own_mono with "Hγf"). apply: auth_frag_mono.
      by apply mnat_included, le_n_S.
    - wp_cas_fail; first (by intros [= ?%Nat2Z.inj]).
      iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c'; by iFrame|].
      iUpdIntro. wp_if. iApply ("IH" with "[Hγf] HΦ").
      rewrite {3}/mcounter; eauto 10.
  Qed.

  Lemma read_mono_spec l j (Φ : val → iProp Σ) :
    mcounter l j ★ (∀ i, ■ (j ≤ i)%nat → mcounter l i -★ Φ #i)
    ⊢ WP read #l {{ Φ }}.
  Proof.
    iIntros "[Hc HΦ]". iDestruct "Hc" as (γ) "(% & #? & #Hinv & Hγf)".
    rewrite /read /=. wp_let. iInv N as (c) ">[Hγ Hl]" "Hclose". wp_load.
    iDestruct (own_valid_2 with "[$Hγ $Hγf]")
      as %[?%mnat_included _]%auth_valid_discrete_2.
    iUpd (own_update_2 with "[$Hγ $Hγf]") as "[Hγ Hγf]".
    { apply auth_update, (mnat_local_update _ _ c); auto. }
    iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[%]"); rewrite /mcounter; eauto 10.
  Qed.
End mono_proof.

(** Counter with contributions *)
Class ccounterG Σ :=
  CCounterG { ccounter_inG :> inG Σ (authR (optionUR (prodR fracR natR))) }.
Definition ccounterΣ : gFunctors :=
  #[GFunctor (constRF (authR (optionUR (prodR fracR natR))))].

Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section contrib_spec.
  Context `{!heapG Σ, !ccounterG Σ} (N : namespace).

  Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (● Some (1%Qp, n)) ★ l ↦ #n)%I.

  Definition ccounter_ctx (γ : gname) (l : loc) : iProp Σ :=
    (heapN ⊥ N ∧ heap_ctx ∧ inv N (ccounter_inv γ l))%I.

  Definition ccounter (γ : gname) (q : frac) (n : nat) : iProp Σ :=
    own γ (◯ Some (q, n)).

  (** The main proofs. *)
  Lemma ccounter_op γ q1 q2 n1 n2 :
    ccounter γ (q1 + q2) (n1 + n2) ⊣⊢ ccounter γ q1 n1★ ccounter γ q2 n2.
  Proof. by rewrite /ccounter -own_op -auth_frag_op. Qed.

  Lemma newcounter_contrib_spec (R : iProp Σ) Φ :
    heapN ⊥ N →
    heap_ctx ★ (∀ γ l, ccounter_ctx γ l ★ ccounter γ 1 0 -★ Φ #l)
    ⊢ WP newcounter #() {{ Φ }}.
  Proof.
    iIntros (?) "[#Hh HΦ]". rewrite /newcounter /=. wp_seq. wp_alloc l as "Hl".
    iUpd (own_alloc (● (Some (1%Qp, O%nat)) ⋅ ◯ (Some (1%Qp, 0%nat))))
      as (γ) "[Hγ Hγ']"; first done.
    iUpd (inv_alloc N _ (ccounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0%nat. by iFrame. }
    iUpdIntro. iApply "HΦ". rewrite /ccounter_ctx /ccounter; eauto 10.
  Qed.

  Lemma inc_contrib_spec γ l q n (Φ : val → iProp Σ) :
    ccounter_ctx γ l ★ ccounter γ q n ★ (ccounter γ q (S n) -★ Φ #())
    ⊢ WP inc #l {{ Φ }}.
  Proof.
    iIntros "(#(%&?&?) & Hγf & HΦ)". iLöb as "IH". wp_rec.
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]" "Hclose".
    wp_load. iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    iUpdIntro. wp_let. wp_op.
    wp_bind (CAS _ _ _). iInv N as (c') ">[Hγ Hl]" "Hclose".
    destruct (decide (c' = c)) as [->|].
    - iUpd (own_update_2 with "[$Hγ $Hγf]") as "[Hγ Hγf]".
      { apply auth_update, option_local_update, prod_local_update_2.
        apply (nat_local_update _ _ (S c) (S n)); omega. }
      wp_cas_suc. iUpd ("Hclose" with "[Hl Hγ]") as "_".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      iUpdIntro. wp_if. by iApply "HΦ".
    - wp_cas_fail; first (by intros [= ?%Nat2Z.inj]).
      iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c'; by iFrame|].
      iUpdIntro. wp_if. by iApply ("IH" with "[Hγf] HΦ").
  Qed.

  Lemma read_contrib_spec γ l q n (Φ : val → iProp Σ) :
    ccounter_ctx γ l ★ ccounter γ q n ★
      (∀ c, ■ (n ≤ c)%nat → ccounter γ q n -★ Φ #c)
    ⊢ WP read #l {{ Φ }}.
  Proof.
    iIntros "(#(%&?&?) & Hγf & HΦ)".
    rewrite /read /=. wp_let. iInv N as (c) ">[Hγ Hl]" "Hclose". wp_load.
    iDestruct (own_valid_2 with "[$Hγ $Hγf]")
      as %[[? ?%nat_included]%Some_pair_included_total_2 _]%auth_valid_discrete_2.
    iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[%]"); rewrite /ccounter; eauto 10.
  Qed.

  Lemma read_contrib_spec_1 γ l n (Φ : val → iProp Σ) :
    ccounter_ctx γ l ★ ccounter γ 1 n ★ (ccounter γ 1 n -★ Φ #n)
    ⊢ WP read #l {{ Φ }}.
  Proof.
    iIntros "(#(%&?&?) & Hγf & HΦ)".
    rewrite /read /=. wp_let. iInv N as (c) ">[Hγ Hl]" "Hclose". wp_load.
    iDestruct (own_valid_2 with "[$Hγ $Hγf]") as %[Hn _]%auth_valid_discrete_2.
    apply (Some_included_exclusive _) in Hn as [= ->]%leibniz_equiv; last done.
    iUpd ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
    by iApply "HΦ".
  Qed.
End contrib_spec.
