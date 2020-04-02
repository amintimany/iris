From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lifting notation.
Set Default Proof Using "Type".

Structure lock Σ `{!heapG Σ} := Lock {
  (* -- operations -- *)
  newlock : val;
  acquire : val;
  release : val;
  (* -- predicates -- *)
  (* name is used to associate locked with is_lock *)
  name : Type;
  is_lock (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (* -- general properties -- *)
  is_lock_ne γ lk : Contractive (is_lock γ lk);
  is_lock_persistent γ lk R : Persistent (is_lock γ lk R);
  is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ↔ R2) -∗ is_lock γ lk R2;
  locked_timeless γ : Timeless (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (* -- operation specs -- *)
  newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}};
  acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}};
  release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}
}.

Arguments newlock {_ _} _.
Arguments acquire {_ _} _.
Arguments release {_ _} _.
Arguments is_lock {_ _} _ _ _ _.
Arguments locked {_ _} _ _.

Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Instance is_lock_proper Σ `{!heapG Σ} (L: lock Σ) γ lk:
  Proper ((≡) ==> (≡)) (is_lock L γ lk) := ne_proper _.
