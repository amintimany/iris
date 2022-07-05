From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import wsat.
From iris.base_logic Require Export later_credits.
From iris.prelude Require Import options.
Export wsatGS.
Import uPred.
Import le_upd_if.

(** The definition of fancy updates (and in turn the logic built on top of it) is parameterized
    by whether it supports elimination of laters via later credits or not.
    This choice is necessary as the fancy update *with* later credits does *not* support
    the interaction laws with the plainly modality in [BiFUpdPlainly]. While these laws are
    seldomly used, support for them is required for backwards compatibility.

    Thus, we define two typeclasses [HasLc] and [HasNoLc].
    The availability of the rules for later credits or the plainly interaction depends
    on having an instance of the right one of these classes in the context. See below.
 *)

Class invGpreS (Σ : gFunctors) : Set := InvGpreS {
  invGpreS_wsat : wsatGpreS Σ;
  invGpreS_lc : lcGpreS Σ;
}.

Class invGS (Σ : gFunctors) : Set := InvG {
  invGS_wsat : wsatGS Σ;
  invGS_lc : lcGS Σ;
  (* flag determining whether the fancy update allows later credit elimination *)
  invGS_use_credits : bool;
}.
Global Hint Mode invGS - : typeclass_instances.
Global Hint Mode invGpreS - : typeclass_instances.
Local Existing Instances invGpreS_wsat invGpreS_lc.
(* [invGS_lc] needs to be global in order to enable the use of lemmas like [lc_split]
   that require [lcGS], and not [invGS].
   [invGS_wsat] also needs to be global as the lemmas in [invariants.v] require it. *)
Global Existing Instances invGS_lc invGS_wsat.

Definition invΣ : gFunctors :=
  #[wsatΣ; lcΣ].
Global Instance subG_invΣ {Σ} : subG invΣ Σ → invGpreS Σ.
Proof. solve_inG. Qed.

(** [HasLc] asserts that the fancy update is defined with support for later credits. *)
Class HasLc (Σ : gFunctors) `{!invGS Σ} :=
  { has_credits : invGS_use_credits = true }.
Global Hint Mode HasLc - - : typeclass_instances.
(** [HasNoLc] asserts that the fancy update is defined without support for later credits,
    but in turn supports the plainly interaction laws [BiFUpdPlainly]. *)
Class HasNoLc (Σ : gFunctors) `{!invGS Σ} :=
  { has_no_credits : invGS_use_credits = false }.
Global Hint Mode HasNoLc - - : typeclass_instances.

Local Definition uPred_fupd_def `{!invGS Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 -∗ le_upd_if invGS_use_credits (◇ (wsat ∗ ownE E2 ∗ P)).
Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {Σ _}.
Local Lemma uPred_fupd_unseal `{!invGS Σ} : @fupd _ uPred_fupd = uPred_fupd_def.
Proof. rewrite -uPred_fupd_aux.(seal_eq) //. Qed.

Lemma uPred_fupd_mixin `{!invGS Σ} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_unseal. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    by iIntros "($ & $ & HE) !> !> [$ $] !> !>" .
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_unseal. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite uPred_fupd_unseal /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance uPred_bi_fupd `{!invGS Σ} : BiFUpd (uPredI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Global Instance uPred_bi_bupd_fupd `{!invGS Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

(** The interaction laws with the plainly modality are only supported when
  we opt out of the support for later credits. *)
Global Instance uPred_bi_fupd_plainly_no_lc `{!invGS Σ, !HasNoLc Σ} :
  BiFUpdPlainly (uPredI (iResUR Σ)).
Proof.
  split; rewrite uPred_fupd_unseal /uPred_fupd_def has_no_credits.
  - iIntros (E P) "H [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    by iFrame.
  - iIntros (E P Q) "[H HQ] [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - iIntros (E P) "H [Hw HE]".
    iAssert (▷ ◇ ■ P)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - iIntros (E A Φ) "HΦ [Hw HE]".
    iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.

Lemma fupd_plain_soundness_no_lc `{!invGpreS Σ} E1 E2 (P: iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS Σ} `{!HasNoLc Σ}, ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc as (Hw) "[Hw HE]".
  iMod (lc_alloc 0) as (Hc) "[_ _]".
  set (Hi := InvG _ Hw Hc false).
  iAssert (|={⊤,E2}=> P)%I as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. iApply Hfupd. by constructor. }
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iMod ("H" with "[$]") as "[Hw [HE >H']]"; iFrame.
Qed.

Lemma step_fupdN_soundness_no_lc `{!invGpreS Σ} φ n :
  (∀ `{Hinv: !invGS Σ} `{!HasNoLc Σ}, ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_plain_soundness_no_lc ⊤ ⊤ _)=> Hinv hc.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iApply fupd_plainly_mask_empty. iMod "H".
  iMod (step_fupdN_plain with "H") as "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iMod "H" as %Hφ. auto.
Qed.

Lemma step_fupdN_soundness_no_lc' `{!invGpreS Σ} φ n :
  (∀ `{Hinv: !invGS Σ} `{!HasNoLc Σ}, ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness_no_lc _ n)=>Hinv Hc. destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod Hiter as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.

(** Later credits: the laws are only available when we opt into later credit support.*)

(** [lc_fupd_elim_later] allows to eliminate a later from a hypothesis at an update.
  This is typically used as [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP".],
  where ["Hcredit"] is a credit available in the context and ["HP"] is the
  assumption from which a later should be stripped. *)
Lemma lc_fupd_elim_later `{!invGS Σ} `{!HasLc Σ} E P :
   £1 -∗ (▷ P) -∗ |={E}=> P.
Proof.
  iIntros "Hf Hupd".
  rewrite uPred_fupd_unseal /uPred_fupd_def has_credits.
  iIntros "[$ $]". iApply (le_upd_later with "Hf").
  iNext. by iModIntro.
Qed.

(** If the goal is a fancy update, this lemma can be used to make a later appear
  in front of it in exchange for a later credit.
  This is typically used as [iApply (lc_fupd_add_later with "Hcredit")],
  where ["Hcredit"] is a credit available in the context. *)
Lemma lc_fupd_add_later `{!invGS Σ} `{!HasLc Σ} E1 E2 P :
  £1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iApply (fupd_trans E1 E1).
  iApply (lc_fupd_elim_later with "Hf Hupd").
Qed.

Lemma fupd_soundness_lc `{!invGpreS Σ} n E1 E2 φ :
  (∀ `{Hinv: !invGS Σ} `{!HasLc Σ}, £ n ⊢@{iPropI Σ} |={E1,E2}=> ⌜φ⌝) → φ.
Proof.
  iIntros (Hfupd). eapply (lc_soundness (S n)). intros Hc.
  rewrite lc_succ.
  iIntros "[Hone Hn]". rewrite -le_upd_trans. iApply bupd_le_upd.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  set (Hi := InvG _ Hw Hc true).
  iAssert (|={⊤,E2}=> ⌜φ⌝)%I with "[Hn]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. by iApply (Hfupd Hi). }
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iModIntro. iMod ("H" with "[$Hw $HE]") as "H".
  iPoseProof (except_0_into_later with "H") as "H".
  iApply (le_upd_later with "Hone"). iNext.
  iDestruct "H" as "(_ & _ & $)".
Qed.

Lemma step_fupdN_soundness_lc `{!invGpreS Σ} φ n m :
  (∀ `{Hinv: !invGS Σ} `{!HasLc Σ}, £ m ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter. eapply (fupd_soundness_lc (m + n)); [apply _..|].
  iIntros (Hinv Hc) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iMod (Hiter with "Hm") as "Hupd".
  clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

Lemma step_fupdN_soundness_lc' `{!invGpreS Σ} φ n m :
  (∀ `{Hinv: !invGS Σ} `{!HasLc Σ}, £ m ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n ⌜ φ ⌝) →
  φ.
Proof.
  intros Hiter. eapply (fupd_soundness_lc (m + n) ⊤ ⊤); [apply _..|].
  iIntros (Hinv Hc) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iPoseProof (Hiter with "Hm") as "Hupd".
  clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

(** Generic soundness lemma for the fancy update, parameterized by [use_credits]
  on whether to use credits or not. *)
Lemma step_fupdN_soundness_gen `{!invGpreS Σ} (φ : Prop)
    (use_credits : bool) (n m : nat) :
  (∀ `{Hinv : invGS Σ} `{Hc : if use_credits then HasLc Σ else HasNoLc Σ},
    (if use_credits then £ m else True) ={⊤,∅}=∗ |={∅}▷=>^n ⌜φ⌝) →
  φ.
Proof.
  destruct use_credits.
  - apply step_fupdN_soundness_lc.
  - apply step_fupdN_soundness_no_lc.
Qed.
