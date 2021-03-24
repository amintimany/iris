From iris.proofmode Require Import string_ident.
From Coq Require Import Strings.String.
From stdpp Require Import base.
Open Scope string.

Lemma test_basic_ident : ∀ (n:nat), n = n.
Proof.
  let x := fresh in intros x; rename_by_string x "n".
  exact (eq_refl n).
Qed.

Check "test_invalid_ident".
Lemma test_invalid_ident : ∀ (n:nat), True.
Proof.
  Fail let x := fresh in intros x; rename_by_string x "has a space".
Abort.

Check "test_not_string".
Lemma test_not_string : ∀ (n:nat), True.
Proof.
  Fail let x := fresh in intros x; rename_by_string x 4.
Abort.

Check "test_not_literal".
Lemma test_not_literal (s:string) : ∀ (n:nat), True.
Proof.
  Fail let x := fresh in intros x; rename_by_string x s.
Abort.
