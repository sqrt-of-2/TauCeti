/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Restricted.Eval
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Analytic substitution of univariate power series

`PowerSeries.analyticSubst f g` has coefficients given by the sums of the coefficients of
`∑ₙ aₙ gⁿ`. If `f` is restricted at `r`, `g` is restricted at a positive radius `s`, and
`‖g‖_s ≤ r`, these sums converge and the result is restricted at `s`. It agrees with evaluation
in the complete Gauss-normed restricted algebra, so in particular it allows nonzero constant
terms in `g`. This radius-independent coefficient formula permits substitution on open discs.
Without convergence hypotheses, the coefficient sums have the usual `tsum` junk values.

The construction uses `PowerSeries.IsRestricted.hasSum_evalAt` in the restricted algebra, not
formal substitution. When formal substitution is defined the two constructions agree.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace PowerSeries

open scoped Topology

section Semiring

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Analytic substitution, defined by the coefficient sums of `∑ₙ coeff n f • gⁿ`.
Use the restrictedness or open-disc hypotheses to ensure convergence. -/
noncomputable def analyticSubst (f g : R⟦X⟧) : R⟦X⟧ :=
  mk fun n ↦ ∑' k, coeff k f * coeff n (g ^ k)

/-- The coefficients of analytic substitution are sums of substituted monomial coefficients. -/
theorem coeff_analyticSubst (f g : R⟦X⟧) (n : ℕ) :
    coeff n (analyticSubst f g) = ∑' k, coeff k f * coeff n (g ^ k) := by
  simp [analyticSubst]

/-- Substitution into a polynomial is ordinary polynomial evaluation, with no convergence
hypothesis on the inner series. -/
@[simp]
theorem analyticSubst_coe (p : Polynomial R) (g : R⟦X⟧) :
    analyticSubst (p : R⟦X⟧) g = Polynomial.aeval g p := by
  ext n
  rw [coeff_analyticSubst, tsum_eq_sum (s := Finset.range (p.natDegree + 1)),
    Polynomial.aeval_eq_sum_range]
  · simp [map_sum]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]

/-- Substituting into a constant gives the same constant. -/
@[simp]
theorem C_analyticSubst (a : R) (g : R⟦X⟧) : analyticSubst (C a) g = C a := by
  simpa using analyticSubst_coe (Polynomial.C a) g

/-- Substituting into zero gives zero. -/
@[simp]
theorem zero_analyticSubst (g : R⟦X⟧) : analyticSubst 0 g = 0 := by
  simpa using analyticSubst_coe (0 : Polynomial R) g

/-- Substituting into one gives one. -/
@[simp]
theorem one_analyticSubst (g : R⟦X⟧) : analyticSubst 1 g = 1 := by
  simpa using analyticSubst_coe (1 : Polynomial R) g

/-- Substituting into the variable gives the inner series. -/
@[simp]
theorem X_analyticSubst (g : R⟦X⟧) : analyticSubst X g = g := by
  simpa using analyticSubst_coe (Polynomial.X : Polynomial R) g

/-- Substitution of a constant is the constant series with value given by analytic evaluation. -/
@[simp]
theorem analyticSubst_C (f : R⟦X⟧) (a : R) :
    analyticSubst f (C a) = C (f.evalAt a) := by
  ext n
  simp only [coeff_analyticSubst, ← map_pow, coeff_C]
  by_cases hn : n = 0
  · simp [hn, evalAt_def, smul_eq_mul]
  · simp [hn]

/-- Substituting the variable itself leaves the series unchanged. -/
@[simp]
theorem analyticSubst_X (f : R⟦X⟧) : analyticSubst f X = f := by
  ext n
  simp [coeff_analyticSubst, coeff_X_pow]

end Semiring

section Ring

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- Whenever formal substitution is defined, analytic substitution agrees with it. -/
theorem analyticSubst_eq_subst (f g : R⟦X⟧) (hg : HasSubst g) :
    analyticSubst f g = f.subst g := by
  ext n
  rw [coeff_analyticSubst, coeff_subst' hg,
    ← tsum_eq_finsum (L := .unconditional _) (coeff_subst_finite' hg f n)]
  simp only [smul_eq_mul]

end Ring

section Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r s : ℝ} [Fact (0 < s)]
  {f g : R⟦X⟧}

/-- The coefficient sums defining analytic substitution converge under the Gauss radius bound. -/
theorem IsRestricted.hasSum_coeff_analyticSubst (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) (n : ℕ) :
    HasSum (fun k ↦ coeff k f * coeff n (g ^ k)) (coeff n (analyticSubst f g)) := by
  let G : IsRestricted.subring (R := R) s := ⟨g, hg⟩
  have hG : ‖G‖ ≤ r := hgr
  have h := (hf.hasSum_evalAt hG).map
    ((coeff n).toAddMonoidHom.comp (IsRestricted.subring (R := R) s).subtype.toAddMonoidHom)
    (TauCeti.PowerSeries.uniformContinuous_coeff n).continuous
  have hs : Summable (fun k ↦ coeff k f * coeff n (g ^ k)) := by
    convert h.summable using 1
    ext k
    simp [Algebra.smul_def, coeff_C_mul, G]
  rw [coeff_analyticSubst]
  exact hs.hasSum

/-- Analytic substitution agrees with evaluation in the complete restricted-series algebra. -/
theorem IsRestricted.analyticSubst_eq_evalAt (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    analyticSubst f g =
      ((f.evalAt (⟨g, hg⟩ : IsRestricted.subring (R := R) s)) :
        IsRestricted.subring (R := R) s).val := by
  let G : IsRestricted.subring (R := R) s := ⟨g, hg⟩
  have hG : ‖G‖ ≤ r := hgr
  ext n
  have h := (hf.hasSum_evalAt hG).map
    ((coeff n).toAddMonoidHom.comp (IsRestricted.subring (R := R) s).subtype.toAddMonoidHom)
    (TauCeti.PowerSeries.uniformContinuous_coeff n).continuous
  exact (hf.hasSum_coeff_analyticSubst hg hgr n).unique (by
    simpa [Function.comp_def, Algebra.smul_def, coeff_C_mul, G] using h)

/-- Substitution preserves restrictedness when the inner Gauss norm is at most the outer radius.
The inner series may have a nonzero constant term. -/
theorem IsRestricted.analyticSubst (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    (analyticSubst f g).IsRestricted s := by
  rw [hf.analyticSubst_eq_evalAt hg hgr]
  exact (f.evalAt (⟨g, hg⟩ : IsRestricted.subring (R := R) s)).2

/-- The Gauss norm of a substitution is bounded by the outer Gauss norm at any admissible
pair of radii. No multiplicativity or norm-one assumption is required. -/
theorem IsRestricted.gaussNorm_analyticSubst_le (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    (PowerSeries.analyticSubst f g).gaussNorm norm s ≤ f.gaussNorm norm r := by
  rw [hf.analyticSubst_eq_evalAt hg hgr, ← TauCeti.PowerSeries.norm_eq_gaussNorm]
  exact norm_evalAt_le_gaussNorm_of_norm_algebraMap_le
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf)
    (fun a ↦ (TauCeti.PowerSeries.norm_algebraMap s a).le) hgr

/-- Substitution is additive on series restricted at the outer radius. -/
theorem IsRestricted.add_analyticSubst {h : R⟦X⟧} (hf : f.IsRestricted r)
    (hh : h.IsRestricted r) (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    PowerSeries.analyticSubst (f + h) g =
      PowerSeries.analyticSubst f g + PowerSeries.analyticSubst h g := by
  have hfh : (f + h).IsRestricted r := hf.add hh
  rw [hfh.analyticSubst_eq_evalAt hg hgr, hf.analyticSubst_eq_evalAt hg hgr,
    hh.analyticSubst_eq_evalAt hg hgr, hf.evalAt_add hh (A := IsRestricted.subring s) hgr]
  rfl

/-- Substitution is multiplicative on series restricted at the outer radius. -/
theorem IsRestricted.mul_analyticSubst {h : R⟦X⟧} (hf : f.IsRestricted r)
    (hh : h.IsRestricted r) (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    PowerSeries.analyticSubst (f * h) g =
      PowerSeries.analyticSubst f g * PowerSeries.analyticSubst h g := by
  have hfh : (f * h).IsRestricted r := hf.mul hh
  rw [hfh.analyticSubst_eq_evalAt hg hgr, hf.analyticSubst_eq_evalAt hg hgr,
    hh.analyticSubst_eq_evalAt hg hgr, hf.evalAt_mul hh (A := IsRestricted.subring s) hgr]
  rfl

end Restricted

end PowerSeries
