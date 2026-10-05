/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar-composition identities and bijectivity under tensoring

Tensoring preserves a composite of linear maps that equals scalar multiplication. This identity
gives bijectivity after extending scalars to a ring in which the scalar is a unit.
-/

public section

namespace TauCeti

open scoped TensorProduct

/-- Tensoring a composite equal to scalar multiplication preserves that identity. -/
theorem lTensor_comp_apply_of_comp_eq_smul {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] N) (f' : N →ₗ[R] M) (s : R) (h : ∀ m, f' (f m) = s • m)
    (x : P ⊗[R] M) : f'.lTensor P (f.lTensor P x) = s • x := by
  have hcomp : f'.comp f = s • LinearMap.id := LinearMap.ext h
  rw [← LinearMap.lTensor_comp_apply, hcomp]
  simp

/-- A linear map with a two-sided inverse up to a scalar becomes bijective after tensoring
with a coefficient algebra in which that scalar is a unit. -/
theorem bijective_lTensor_of_comp_eq_smul {R A M N : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (f' : N →ₗ[R] M) (s : R)
    (hf'f : ∀ m, f' (f m) = s • m) (hff' : ∀ n, f (f' n) = s • n)
    (hs : IsUnit (algebraMap R A s)) : Function.Bijective (f.lTensor A) := by
  obtain ⟨u, hu⟩ := hs
  have hf'fA (x : A ⊗[R] M) : f'.lTensor A (f.lTensor A x) = (u : A) • x := by
    rw [lTensor_comp_apply_of_comp_eq_smul f f' s hf'f,
      ← IsScalarTower.algebraMap_smul A, ← hu]
  have hff'A (y : A ⊗[R] N) : f.lTensor A (f'.lTensor A y) = (u : A) • y := by
    rw [lTensor_comp_apply_of_comp_eq_smul f' f s hff',
      ← IsScalarTower.algebraMap_smul A, ← hu]
  refine ⟨fun x y hxy ↦ u.isUnit.smul_left_cancel.mp ?_, fun y ↦ ?_⟩
  · simpa only [hf'fA] using congrArg (f'.lTensor A) hxy
  · refine ⟨(↑u⁻¹ : A) • f'.lTensor A y, ?_⟩
    rw [← LinearMap.baseChange_eq_ltensor, map_smul, LinearMap.baseChange_eq_ltensor,
      hff'A, smul_smul, Units.inv_mul, one_smul]

end TauCeti
