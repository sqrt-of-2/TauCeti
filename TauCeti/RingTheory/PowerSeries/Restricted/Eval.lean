/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.TateAlgebra

/-!
# Continuous evaluation of Gauss-normed restricted series

Evaluation at an element bounded by the radius is continuous for the Gauss norm when the
coefficient embedding is contractive. The target algebra may be noncommutative and need not
have norm-one identity. This lets continuous algebra maps act on convergent substitutions.
-/

public section

namespace PowerSeries

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedRing A] [Algebra R A] [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A]
  {s : ℝ} [Fact (0 < s)]

/-- Restricted evaluation along a contractive coefficient embedding is continuous for the
positive-radius Gauss norm, including in noncommutative target algebras. -/
@[continuity]
theorem IsRestricted.continuous_evalAtHom (hφ : ∀ a, ‖algebraMap R A a‖ ≤ ‖a‖)
    {b : A} (hb : ‖b‖ ≤ s) : Continuous (IsRestricted.evalAtHom R hb) := by
  apply AddMonoidHomClass.continuous_of_bound _ 1
  intro F
  simpa [TauCeti.PowerSeries.norm_eq_gaussNorm] using
    norm_evalAt_le_gaussNorm_of_norm_algebraMap_le
      (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted F.2) hφ hb

end PowerSeries
