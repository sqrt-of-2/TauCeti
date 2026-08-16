/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Commutators in associative rings

This file records identities for moving elements past powers when their ring commutator is an
integer multiple of one of the elements or commutes with the powered element, together with a
nilpotency criterion for a commutator that is central for both of its arguments.

## Main results

* `TauCeti.Associative.mul_pow_eq_pow_mul_add_zsmul`: moving an element past a power of an
  integer-eigenvector for its commutator.
* `TauCeti.Associative.mul_pow_eq_pow_mul_add_intCast`: the same identity in shifted-factor form.
* `TauCeti.Associative.mul_pow_of_commutator_eq`: moving an element past a power when the
  commutator commutes with the powered element.
* `TauCeti.Associative.isNilpotent_of_commutator_eq`: a commutator commuting with both of its
  arguments is nilpotent as soon as one of them is.
-/

public section

namespace TauCeti.Associative

variable {A : Type*} [Ring A] {x y : A} {c : ℤ}

/-- If `y` has integer eigenvalue `c` for commutation with `x`, then moving `x` past `yⁿ`
adds `n * c` copies of `yⁿ`. -/
theorem mul_pow_eq_pow_mul_add_zsmul (hxy : x * y - y * x = c • y) (n : ℕ) :
    x * y ^ n = y ^ n * x + ((n : ℤ) * c) • y ^ n := by
  have hy : x * y = y * x + c • y := by
    rw [← hxy]
    abel
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * y ^ (n + 1) = x * y ^ n * y := by rw [pow_succ, ← mul_assoc]
      _ = (y ^ n * x + ((n : ℤ) * c) • y ^ n) * y := by rw [ih]
      _ = y ^ n * (x * y) + ((n : ℤ) * c) • y ^ (n + 1) := by
          rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
      _ = y ^ n * (y * x + c • y) + ((n : ℤ) * c) • y ^ (n + 1) := by rw [hy]
      _ = y ^ (n + 1) * x + (c + (n : ℤ) * c) • y ^ (n + 1) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, mul_smul_comm, ← pow_succ, add_assoc, ← add_smul]
      _ = y ^ (n + 1) * x + (((n + 1 : ℕ) : ℤ) * c) • y ^ (n + 1) := by
          push_cast
          ring_nf

/-- The shifted-factor form of `mul_pow_eq_pow_mul_add_zsmul`. -/
theorem mul_pow_eq_pow_mul_add_intCast (hxy : x * y - y * x = c • y) (n : ℕ) :
    x * y ^ n = y ^ n * (x + (c : A) * (n : A)) := by
  rw [mul_pow_eq_pow_mul_add_zsmul hxy, zsmul_eq_mul', mul_add, Int.cast_mul,
    Int.cast_natCast, (Nat.cast_commute n (c : A)).eq]

/-- Moving one element across an ordinary power when its commutator commutes with the element being
powered. -/
theorem mul_pow_of_commutator_eq {A : Type*} [Semiring A] {x y z : A}
    (hxy : x * y = y * x + z) (hyz : Commute y z) (n : ℕ) :
    x * y ^ n = y ^ n * x + n • (y ^ (n - 1) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simpa using hxy
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc (y ^ (n + 1)) x y,
            hxy, mul_add]
          -- Expose the final successor separately: rewriting `add_nsmul` on `n + 2` directly
          -- would split the coefficient as `n` and `2`, rather than the required `n + 1` and `1`.
          rw [show n + 2 = (n + 1) + 1 by omega, add_nsmul, one_nsmul]
          noncomm_ring [hyz.eq, pow_succ]
          simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, mul_one]
          noncomm_ring

section CentralCommutator

variable {A : Type*} [Ring A] [IsAddTorsionFree A] {x y z : A}

/-- **Nilpotency of a central commutator.** If `x * y = y * x + z` with `z` commuting with both `x`
and `y` in an additively torsion-free ring, then `z` is nilpotent as soon as `x` is. -/
theorem isNilpotent_of_commutator_eq (hxy : x * y = y * x + z) (hxz : Commute x z)
    (hyz : Commute y z) (hx : IsNilpotent x) : IsNilpotent z := by
  obtain ⟨n, hn⟩ := hx
  -- Moving `y` past a power of `x` releases that many copies of the commutator.
  have hpow (m : ℕ) : x ^ (m + 1) * y = y * x ^ (m + 1) + (m + 1) • (z * x ^ m) := by
    have h := mul_pow_of_commutator_eq (x := y) (y := x) (z := -z)
      (by rw [hxy]; abel) hxz.neg_right (m + 1)
    simp only [Nat.add_sub_cancel, mul_neg] at h
    rw [(hxz.pow_left m).eq] at h
    simp only [smul_neg] at h
    exact sub_eq_iff_eq_add.mp (by simpa [sub_eq_add_neg] using h.symm)
  -- Each copy of `z` extracted this way lowers the power of `x` that annihilates it.
  have hstep : ∀ m k : ℕ, x ^ (m + 1) * z ^ k = 0 → x ^ m * z ^ (k + 1) = 0 := by
    intro m k h
    -- Pushing `y` to the right kills the product outright.
    have hA : x ^ (m + 1) * y * z ^ k = 0 := by
      rw [mul_assoc, ← (hyz.symm.pow_left k).eq, ← mul_assoc, h, zero_mul]
    -- Pushing it to the left leaves the released copies of `z`.
    have hB : x ^ (m + 1) * y * z ^ k = (m + 1) • (x ^ m * z ^ (k + 1)) := by
      rw [hpow m, add_mul, mul_assoc, h, mul_zero, zero_add, smul_mul_assoc,
        (hxz.symm.pow_right m).eq, mul_assoc, ← pow_succ']
    apply (nsmul_eq_zero_iff_right m.succ_ne_zero).mp
    rw [← hB]
    exact hA
  -- Peel the powers of `x` off one at a time.
  have hpeel : ∀ k ≤ n, x ^ (n - k) * z ^ k = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hn
    | succ k ih =>
      intro hk
      have heq : n - k = n - (k + 1) + 1 := by omega
      exact hstep (n - (k + 1)) k (by rw [← heq]; exact ih (by omega))
  exact ⟨n, by simpa using hpeel n le_rfl⟩

end CentralCommutator

end TauCeti.Associative
