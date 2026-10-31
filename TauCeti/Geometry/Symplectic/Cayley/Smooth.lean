/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Smooth compatible Cayley interpolation

The algebraic Cayley chart identifies compatible complex structures with a convex ball of
self-adjoint antilinear endomorphisms. Here its inverse is shown to preserve smooth parameter
families, using the operator-norm topology on continuous linear maps. This is needed when
extending prescribed almost complex structures across collars: convex interpolation must be
smooth as well as pointwise compatible.

`SymplecticForm.Compatible.cayleyPath` joins a compatible structure to any other compatible
structure, is constant for parameters at most zero and at least one, and is smooth on the
whole real line. Thus its endpoint jets of every positive order vanish. Smoothness is also
proved jointly with external parameters for families expressed in Cayley coordinates. These
are linear, fixed-form statements; no extension theorem for sections of a tangent bundle is
asserted here.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart on compatible complex structures).
-/

public noncomputable section

open Set Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ J₁ : AlmostComplexStructure V}

/-- In operator-norm coordinates, the inverse compatible Cayley chart is the same rational
formula as its algebraic version. -/
theorem Compatible.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap
    (h₀ : ω.Compatible J₀) (C : V →L[ℝ] V)
    (hC : C.toLinearMap ∈ ω.compatibleCayleyBall J₀) :
    LinearMap.toContinuousLinearMap
        (h₀.compatibleCayleyEquiv.symm ⟨C.toLinearMap, hC⟩).val.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := by
  have hunit : IsUnit (1 - C) := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
    exact isUnit_one_sub_of_mem_cayleyBall (mem_compatibleCayleyBall.1 hC).1
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap]
  rw [Compatible.compatibleCayleyEquiv_symm_apply_toLinearMap]
  have hinv := hunit.map_ringInverse (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ))
  simpa only [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_one, LinearMap.coe_toContinuousLinearMap,
    ContinuousLinearMap.toLinearMapRingHom_apply, map_sub, map_one] using
    congrArg (fun A => J₀.toLinearMap * (1 + C.toLinearMap) * A) hinv.symm

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A smooth family in the compatible Cayley ball gives a smooth family of compatible
structures. Smoothness is in the continuous-endomorphism carrier, so it includes all external
parameters of the family. -/
theorem Compatible.contDiffAt_compatibleCayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀)
    {n : WithTop ℕ∞} {p : P} (hCs : ContDiffAt ℝ n C p) :
    ContDiffAt ℝ n (fun q => LinearMap.toContinuousLinearMap
      (h₀.compatibleCayleyEquiv.symm ⟨(C q).toLinearMap, hC q⟩).val.toLinearMap) p := by
  simp_rw [h₀.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap]
  have hunit : IsUnit (1 - C p) := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
    exact isUnit_one_sub_of_mem_cayleyBall (mem_compatibleCayleyBall.1 (hC p)).1
  obtain ⟨u, hu⟩ := hunit
  have hi : ContDiffAt ℝ n (fun q => Ring.inverse (1 - C q)) p := by
    have hi := contDiffAt_ringInverse (n := n) ℝ u
    rw [hu] at hi
    exact hi.comp p (contDiffAt_const.sub hCs)
  exact (contDiffAt_const.mul (contDiffAt_const.add hCs)).mul hi

/-- The inverse compatible Cayley chart preserves globally smooth parameter families. -/
theorem Compatible.contDiff_compatibleCayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀)
    {n : WithTop ℕ∞} (hCs : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => LinearMap.toContinuousLinearMap
      (h₀.compatibleCayleyEquiv.symm ⟨(C p).toLinearMap, hC p⟩).val.toLinearMap) :=
  contDiff_iff_contDiffAt.2 fun _ => h₀.contDiffAt_compatibleCayleyEquiv_symm hC hCs.contDiffAt

/-- Multiplying a compatible Cayley coordinate by a scalar between zero and one stays in the
compatible Cayley ball. -/
theorem Compatible.smul_cayley_mem_compatibleCayleyBall (h₀ : ω.Compatible J₀)
    (h₁ : ω.Compatible J₁) {t : ℝ} (ht : t ∈ Icc 0 1) :
    t • J₀.cayley J₁ ∈ ω.compatibleCayleyBall J₀ := by
  have h := h₀.tames.convex_compatibleCayleyBall h₀.tames.zero_mem_compatibleCayleyBall
    ((h₀.cayley_mem_compatibleCayleyBall_iff h₁.tames).2 h₁)
    (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simpa only [smul_zero, zero_add] using h

/-- A smooth, collar-constant path from `J₀` to `J₁` through compatible structures, obtained by
multiplying the Cayley coordinate of `J₁` by `smoothTransition t`. -/
def Compatible.cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    AlmostComplexStructure V :=
  (h₀.compatibleCayleyEquiv.symm
    ⟨smoothTransition t • J₀.cayley J₁,
      h₀.smul_cayley_mem_compatibleCayleyBall h₁
        ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩⟩).val

/-- The interpolated structure is compatible at every parameter, not only at its endpoints. -/
theorem Compatible.compatible_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    ω.Compatible (h₀.cayleyPath h₁ t) :=
  (h₀.compatibleCayleyEquiv.symm _).property

/-- The Cayley coordinate of the path is the cutoff-scaled coordinate of its endpoint. -/
@[simp]
theorem Compatible.cayley_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    J₀.cayley (h₀.cayleyPath h₁ t) = smoothTransition t • J₀.cayley J₁ := by
  unfold Compatible.cayleyPath
  simpa only [Compatible.compatibleCayleyEquiv_apply_coe] using
    congrArg Subtype.val (h₀.compatibleCayleyEquiv.apply_symm_apply
      ⟨smoothTransition t • J₀.cayley J₁,
        h₀.smul_cayley_mem_compatibleCayleyBall h₁
          ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩⟩)

/-- Interpolating a structure with itself leaves it fixed at every parameter. -/
@[simp]
theorem Compatible.cayleyPath_self (h₀ : ω.Compatible J₀) (t : ℝ) :
    h₀.cayleyPath h₀ t = J₀ := by
  have h := h₀.compatibleCayleyEquiv.injective (a₁ :=
      ⟨h₀.cayleyPath h₀ t, h₀.compatible_cayleyPath h₀ t⟩) (a₂ := ⟨J₀, h₀⟩)
    (Subtype.ext (by simp))
  exact congrArg Subtype.val h

/-- The path agrees with its initial structure on the entire incoming collar. -/
@[simp]
theorem Compatible.cayleyPath_of_nonpos (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    {t : ℝ} (ht : t ≤ 0) : h₀.cayleyPath h₁ t = J₀ := by
  have h := h₀.compatibleCayleyEquiv.injective (a₁ :=
      ⟨h₀.cayleyPath h₁ t, h₀.compatible_cayleyPath h₁ t⟩) (a₂ := ⟨J₀, h₀⟩)
    (Subtype.ext (by simp [h₀.cayley_cayleyPath, smoothTransition.zero_of_nonpos ht]))
  exact congrArg Subtype.val h

/-- The path agrees with its final structure on the entire outgoing collar. -/
@[simp]
theorem Compatible.cayleyPath_of_one_le (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    {t : ℝ} (ht : 1 ≤ t) : h₀.cayleyPath h₁ t = J₁ := by
  have h := h₀.compatibleCayleyEquiv.injective (a₁ :=
      ⟨h₀.cayleyPath h₁ t, h₀.compatible_cayleyPath h₁ t⟩) (a₂ := ⟨J₁, h₁⟩)
    (Subtype.ext (by simp [h₀.cayley_cayleyPath, smoothTransition.one_of_one_le ht]))
  exact congrArg Subtype.val h

/-- The path is smooth on the whole real line, including both transition endpoints. -/
theorem Compatible.contDiff_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    (n : ℕ∞) :
    ContDiff ℝ n (fun t => LinearMap.toContinuousLinearMap (h₀.cayleyPath h₁ t).toLinearMap) := by
  let C : ℝ → V →L[ℝ] V := fun t =>
    smoothTransition t • LinearMap.toContinuousLinearMap (J₀.cayley J₁)
  have hC (t : ℝ) : (C t).toLinearMap ∈ ω.compatibleCayleyBall J₀ := by
    exact h₀.smul_cayley_mem_compatibleCayleyBall h₁
      ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩
  exact h₀.contDiff_compatibleCayleyEquiv_symm hC
    (smoothTransition.contDiff.smul contDiff_const)

end TauCeti.SymplecticForm
