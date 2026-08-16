/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.NormalOrdering
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
import Mathlib.Algebra.Module.Rat

/-!
# The Chevalley commutator relation for integral nilpotent exponentials

Let `V` be a module over a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and let
`x`, `y`, `z` be elements of `A` with

```text
x * y = y * x + z,   z commuting with both x and y.
```

The integral divided-power exponentials of `x`, `y`, `z` act on the scalar extension `R ⊗[ℤ] M`
over every commutative ring `R`, by `TauCeti.baseChangeExp`. The main result below is that they
satisfy the **Chevalley commutator relation**

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t).
```

Equivalently `E_x(t) E_y(u) E_x(t)⁻¹ = E_y(u) E_z(t * u)`: conjugating the one-parameter subgroup
of `y` by the one-parameter subgroup of `x` multiplies it by the one-parameter subgroup of the
commutator, at the product parameter. This is the class-two case of the Chevalley commutator
formula, the case in which the only root of the form `i α + j β` besides `α` and `β` is `α + β`;
in a simply-laced root system every pair of non-proportional roots falls under it or under the
degenerate case below.

Nothing here divides by a factorial in `R`, so the relation holds over a ring of arbitrary
characteristic. The whole point is the coefficient-one normal-ordering rule
`TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq`, which says that the
rational divided powers reorder with integral structure constants; the exponential identity is
its generating-function form.

## Main results

* `TauCeti.integralDividedPower_mul_integralDividedPower_of_commutator_eq`: normal ordering for the
  integral operators restricted to `M`.
* `TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq`: the Chevalley commutator relation.
* `TauCeti.baseChangeExp_conj_of_commutator_eq`: its conjugation form.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4 and Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti

open Finset TensorProduct

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-! ## Normal ordering the restricted operators -/

/-- **Normal ordering for restricted divided powers.** If `x * y = y * x + z` and `z` commutes with
both `x` and `y`, the integral operators obtained by restricting divided powers to a stable additive
subgroup satisfy the coefficient-one straightening rule. -/
theorem integralDividedPower_mul_integralDividedPower_of_commutator_eq
    {x y z : A} (M : S) (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (m n : ℕ) :
    integralDividedPower x M m (hMx m) * integralDividedPower y M n (hMy n) =
      ∑ k ∈ range (min m n + 1),
        integralDividedPower y M (n - k) (hMy (n - k)) *
          integralDividedPower z M k (hMz k) *
          integralDividedPower x M (m - k) (hMx (m - k)) := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum,
    coe_integralDividedPower_apply, ← mul_smul, ← Finset.sum_smul]
  congr 1
  simpa only [mul_assoc] using
    Associative.dividedPower_mul_dividedPower_of_commutator_eq hxy hxz hyz m n

/-! ## The generating-function form of normal ordering -/

-- The combinatorial core: a truncated left factor times a truncated right factor is the reordered
-- triple product, once the truncation is wide enough that the reindexed square contains no extra
-- nonzero terms. The reindexing is `(m, n, k) ↦ (n - k, k, m - k)`.
private theorem sum_smul_mul_sum_smul_of_normalOrder {R : Type*} [CommRing R]
    {B : Type*} [Ring B] [Algebra R B] (Dx Dy Dz : ℕ → B) (N : ℕ)
    (hno : ∀ m n, Dx m * Dy n =
      ∑ k ∈ range (min m n + 1), Dy (n - k) * Dz k * Dx (m - k))
    (hzero : ∀ p k q : ℕ, N ≤ p + k ∨ N ≤ q + k → Dy p * Dz k * Dx q = 0)
    (t u : R) :
    (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) =
      (∑ p ∈ range N, u ^ p • Dy p) * (∑ k ∈ range N, (t * u) ^ k • Dz k) *
        (∑ q ∈ range N, t ^ q • Dx q) := by
  classical
  set G : ℕ × ℕ × ℕ → B := fun w =>
    (u ^ w.1 * (t * u) ^ w.2.1 * t ^ w.2.2) • (Dy w.1 * Dz w.2.1 * Dx w.2.2) with hG
  -- Step 1: expand the reordered product over the full cube of indices.
  have hbox : ∑ w ∈ range N ×ˢ range N ×ˢ range N, G w =
      (∑ p ∈ range N, u ^ p • Dy p) * (∑ k ∈ range N, (t * u) ^ k • Dz k) *
        (∑ q ∈ range N, t ^ q • Dx q) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [hG, Finset.sum_product, Finset.mul_sum, smul_mul_smul_comm, mul_assoc]
  -- Step 2: expand the original product over the reindexing domain.
  have hsrc : ∑ w ∈ (range N ×ˢ range N).sigma (fun mn => range (min mn.1 mn.2 + 1)),
        (t ^ w.1.1 * u ^ w.1.2) • (Dy (w.1.2 - w.2) * Dz w.2 * Dx (w.1.1 - w.2)) =
      (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) := by
    rw [Finset.sum_sigma, Finset.sum_mul_sum]
    simp only [Finset.sum_product, smul_mul_smul_comm, hno, Finset.smul_sum]
  -- Step 3: the reindexing itself, onto the part of the cube it covers.
  have hbij : ∑ w ∈ (range N ×ˢ range N).sigma (fun mn => range (min mn.1 mn.2 + 1)),
        (t ^ w.1.1 * u ^ w.1.2) • (Dy (w.1.2 - w.2) * Dz w.2 * Dx (w.1.1 - w.2)) =
      ∑ w ∈ range N ×ˢ range N ×ˢ range N with w.1 + w.2.1 < N ∧ w.2.2 + w.2.1 < N, G w := by
    refine Finset.sum_nbij' (fun w => (w.1.2 - w.2, w.2, w.1.1 - w.2))
      (fun w => ⟨(w.2.2 + w.2.1, w.1 + w.2.1), w.2.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨m, n⟩, k⟩ hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
        le_min_iff] at hw
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · rintro ⟨p, k, q⟩ hw
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
        le_min_iff]
      omega
    · rintro ⟨⟨m, n⟩, k⟩ hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
        le_min_iff] at hw
      dsimp only
      rw [Nat.sub_add_cancel hw.2.1, Nat.sub_add_cancel hw.2.2]
    · rintro ⟨p, k, q⟩ _
      simp
    · rintro ⟨⟨m, n⟩, k⟩ hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
        le_min_iff] at hw
      obtain ⟨a, rfl⟩ : ∃ a, m = a + k := ⟨m - k, (Nat.sub_add_cancel hw.2.1).symm⟩
      obtain ⟨b, rfl⟩ : ∃ b, n = b + k := ⟨n - k, (Nat.sub_add_cancel hw.2.2).symm⟩
      simp only [hG, Nat.add_sub_cancel]
      congr 1
      rw [mul_pow]
      ring
  -- Step 4: the terms of the cube outside that part vanish.
  have hsub : ∑ w ∈ range N ×ˢ range N ×ˢ range N with w.1 + w.2.1 < N ∧ w.2.2 + w.2.1 < N,
        G w = ∑ w ∈ range N ×ˢ range N ×ˢ range N, G w := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    rintro ⟨p, k, q⟩ hmem hnot
    simp only [Finset.mem_product, Finset.mem_range] at hmem
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hnot
    have hor : N ≤ p + k ∨ N ≤ q + k := by omega
    simp [hG, hzero p k q hor]
  rw [← hsrc, hbij, hsub, hbox]

/-! ## The Chevalley commutator relation -/

section Commutator

variable {R : Type v} [CommRing R] [Algebra ℤ R]

-- Match tensor products to the module structure carried by the explicit `ℤ`-algebra.
attribute [local instance high] Algebra.toModule

/-- **The Chevalley commutator relation for integral nilpotent exponentials.** If
`x * y = y * x + z` with `z` commuting with `x` and with `y`, then over every commutative ring `R`
the integral divided-power exponentials on `R ⊗[ℤ] M` satisfy

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t).
```

No factorial is inverted in `R`: the relation holds in every characteristic. -/
theorem baseChangeExp_mul_baseChangeExp_of_commutator_eq
    {x y z : A} (M : S) (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) (hy : IsNilpotent y)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) * baseChangeExp x M hMx t := by
  classical
  let _ := IsAddTorsionFree.of_module_rat A
  obtain ⟨kz, hkz⟩ := Associative.isNilpotent_of_commutator_eq hxy hxz hyz hx
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  set N := kx + ky + kz with hNdef
  have hxN : x ^ N = 0 := pow_eq_zero_of_le (by omega) hkx
  have hyN : y ^ N = 0 := pow_eq_zero_of_le (by omega) hky
  have hzN : z ^ N = 0 := pow_eq_zero_of_le (by omega) hkz
  rw [baseChangeExp_of_pow_eq_zero x M hMx hxN,
    baseChangeExp_of_pow_eq_zero y M hMy hyN,
    baseChangeExp_of_pow_eq_zero z M hMz hzN]
  refine sum_smul_mul_sum_smul_of_normalOrder (R := R)
    (fun n => (integralDividedPower x M n (hMx n)).baseChange R)
    (fun n => (integralDividedPower y M n (hMy n)).baseChange R)
    (fun n => (integralDividedPower z M n (hMz n)).baseChange R) N ?_ ?_ t u
  · intro m n
    have h := congrArg (fun f : Module.End ℤ M => (Module.End.baseChangeHom ℤ R M) f)
      (integralDividedPower_mul_integralDividedPower_of_commutator_eq M hxy hxz hyz hMx hMy hMz m n)
    simp only [map_mul, map_sum] at h
    exact h
  · -- Outside the truncation the reordered triple has a vanishing factor.
    have hvx : ∀ q, kx ≤ q → (integralDividedPower x M q (hMx q)).baseChange R = 0 := by
      intro q hq
      rw [integralDividedPower_eq_zero_of_le x M q (hMx q) hkx hq, LinearMap.baseChange_zero]
    have hvy : ∀ p, ky ≤ p → (integralDividedPower y M p (hMy p)).baseChange R = 0 := by
      intro p hp
      rw [integralDividedPower_eq_zero_of_le y M p (hMy p) hky hp, LinearMap.baseChange_zero]
    have hvz : ∀ k, kz ≤ k → (integralDividedPower z M k (hMz k)).baseChange R = 0 := by
      intro k hk
      rw [integralDividedPower_eq_zero_of_le z M k (hMz k) hkz hk, LinearMap.baseChange_zero]
    rintro p k q (hpk | hqk)
    · rcases le_or_gt ky p with hp | hp
      · rw [hvy p hp, zero_mul, zero_mul]
      · rw [hvz k (by omega), mul_zero, zero_mul]
    · rcases le_or_gt kx q with hq | hq
      · rw [hvx q hq, mul_zero]
      · rw [hvz k (by omega), mul_zero, zero_mul]

/-- The conjugation form of the Chevalley commutator relation: conjugating the one-parameter
subgroup of `y` by that of `x` multiplies it by the one-parameter subgroup of the commutator `z`,
at the product parameter. -/
theorem baseChangeExp_conj_of_commutator_eq
    {x y z : A} (M : S) (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) (hy : IsNilpotent y)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u * baseChangeExp x M hMx (-t) =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) := by
  rw [baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy hxz hyz hx hy hMx hMy hMz t u,
    mul_assoc, ← baseChangeExp_add x M hMx hx t (-t), add_neg_cancel,
    baseChangeExp_zero x M hMx hx, mul_one]

end Commutator

end TauCeti
