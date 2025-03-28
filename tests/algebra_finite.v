From iris.algebra Require Import ofe stepindex_finite.

(** Test that [decide] finds the instance for [Nat], not [SIdx.eq_dec]. *)
Goal ∀ n1 n2 : nat, decide (n1 = n2) = Nat.eq_dec n1 n2.
Proof. done. Qed.

Goal ∀ (A : ofe) n (x1 x2 : later A), Next x1 ≡{n}≡ Next x2.
Proof.
  intros A n x1 x2. f_contractive_fin.
  Show. (* Goal should be [x1 ≡{n}≡ x2], not [x1 ≡{n'}≡ x2] with [n' < n] *)
Abort.
