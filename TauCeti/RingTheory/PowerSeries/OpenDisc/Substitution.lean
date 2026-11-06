/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.AnalyticSubst
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval

/-!
# Analytic substitution on open discs

Let `f` be analytic on the open disc of radius `U` and `g` on the open disc of positive
radius `V`. If `‖g‖_s < U` at every `0 < s < V`, then `f(g)` is analytic on the open disc
of radius `V`. The radius control is in Gauss norms, rather than pointwise values, and the
constant term of `g` need not vanish. At each smaller radius the substitution agrees with
evaluation in the complete restricted-series algebra.

`PowerSeries.OnOpenDisc.analyticSubstHom` bundles this operation as a ring homomorphism.
Its coefficients are the convergent sums of the substituted monomial coefficients. In
particular it extends polynomial evaluation and agrees with formal substitution whenever
that is defined.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace PowerSeries

open scoped Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {U V : ℝ} {f g : R⟦X⟧}

/-- Analytic substitution preserves the open-disc radius condition when the inner Gauss norms
stay strictly below the outer disc radius. -/
theorem OnOpenDisc.analyticSubst (hf : f.OnOpenDisc U) (hg : g.OnOpenDisc V)
    (hbound : ∀ s, 0 < s → s < V → g.gaussNorm norm s < U) :
    (PowerSeries.analyticSubst f g).OnOpenDisc V := by
  apply onOpenDisc_iff.mpr
  intro s hs hsV
  have : Fact (0 < s) := ⟨hs⟩
  obtain ⟨r, hgr, hrU⟩ := exists_between (hbound s hs hsV)
  have hr : 0 < r := (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr
  exact ((onOpenDisc_iff.mp hf) r hr hrU).analyticSubst
    ((onOpenDisc_iff.mp hg) s hs hsV) hgr.le

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Choose one pair of closed subdiscs for the coefficient and ring-law proofs. -/
private theorem exists_substitution_radii
    (hbound : ∀ s, 0 < s → s < V → g.gaussNorm norm s < U) (hV : 0 < V) :
    ∃ s r, 0 < s ∧ s < V ∧ 0 < r ∧ r < U ∧ g.gaussNorm norm s ≤ r := by
  obtain ⟨s, hs, hsV⟩ := exists_between hV
  obtain ⟨r, hgr, hrU⟩ := exists_between (hbound s hs hsV)
  exact ⟨s, r, hs, hsV, (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr, hrU, hgr.le⟩

/-- Under the open-disc radius control, the coefficient sums defining substitution converge. -/
theorem OnOpenDisc.hasSum_coeff_analyticSubst (hf : f.OnOpenDisc U) (hg : g.OnOpenDisc V)
    (hbound : ∀ s, 0 < s → s < V → g.gaussNorm norm s < U)
    (hV : 0 < V) (n : ℕ) :
    HasSum (fun k ↦ coeff k f * coeff n (g ^ k))
      (coeff n (PowerSeries.analyticSubst f g)) := by
  obtain ⟨s, r, hs, hsV, hr, hrU, hgr⟩ := exists_substitution_radii hbound hV
  have : Fact (0 < s) := ⟨hs⟩
  exact ((onOpenDisc_iff.mp hf) r hr hrU).hasSum_coeff_analyticSubst
    ((onOpenDisc_iff.mp hg) s hs hsV) hgr n

/-- At admissible closed subdiscs, substitution satisfies the same Gauss bound as restricted
analytic substitution. -/
theorem OnOpenDisc.gaussNorm_analyticSubst_le (hf : f.OnOpenDisc U) (hg : g.OnOpenDisc V)
    {r s : ℝ} (hr : 0 < r) (hrU : r < U) (hs : 0 < s) (hsV : s < V)
    (hgr : g.gaussNorm norm s ≤ r) :
    (PowerSeries.analyticSubst f g).gaussNorm norm s ≤ f.gaussNorm norm r := by
  have : Fact (0 < s) := ⟨hs⟩
  exact ((onOpenDisc_iff.mp hf) r hr hrU).gaussNorm_analyticSubst_le
    ((onOpenDisc_iff.mp hg) s hs hsV) hgr

namespace OnOpenDisc

variable (g) (hg : g.OnOpenDisc V)
  (hbound : ∀ s, 0 < s → s < V → g.gaussNorm norm s < U) (hV : 0 < V)

/-- Substitution by an analytic map of open discs, with explicit Gauss-radius control.
Nonzero constant terms of the inner series are allowed. -/
noncomputable def analyticSubstHom : OnOpenDisc.subring R U →+* OnOpenDisc.subring R V where
  toFun f := ⟨PowerSeries.analyticSubst f g,
    mem_subring.mpr ((mem_subring.mp f.2).analyticSubst hg hbound)⟩
  map_zero' := Subtype.ext (zero_analyticSubst g)
  map_one' := Subtype.ext (one_analyticSubst g)
  map_add' f h := by
    obtain ⟨s, r, hs, hsV, hr, hrU, hgr⟩ := exists_substitution_radii hbound hV
    have : Fact (0 < s) := ⟨hs⟩
    exact Subtype.ext (((onOpenDisc_iff.mp (mem_subring.mp f.2)) r hr hrU).add_analyticSubst
      ((onOpenDisc_iff.mp (mem_subring.mp h.2)) r hr hrU)
      ((onOpenDisc_iff.mp hg) s hs hsV) hgr)
  map_mul' f h := by
    obtain ⟨s, r, hs, hsV, hr, hrU, hgr⟩ := exists_substitution_radii hbound hV
    have : Fact (0 < s) := ⟨hs⟩
    exact Subtype.ext (((onOpenDisc_iff.mp (mem_subring.mp f.2)) r hr hrU).mul_analyticSubst
      ((onOpenDisc_iff.mp (mem_subring.mp h.2)) r hr hrU)
      ((onOpenDisc_iff.mp hg) s hs hsV) hgr)

/-- On underlying series the substitution homomorphism is analytic substitution. -/
@[simp]
theorem coe_analyticSubstHom (f : OnOpenDisc.subring R U) :
    (analyticSubstHom g hg hbound hV f : R⟦X⟧) = PowerSeries.analyticSubst f g := (rfl)

/-- Substitution sends constants to the same constants. -/
@[simp]
theorem analyticSubstHom_C (a : R) :
    analyticSubstHom g hg hbound hV ⟨C a, mem_subring.mpr (onOpenDisc_C a)⟩ =
      ⟨C a, mem_subring.mpr (onOpenDisc_C a)⟩ :=
  Subtype.ext (C_analyticSubst a g)

/-- Substitution sends the variable to the given inner series. -/
@[simp]
theorem analyticSubstHom_X :
    analyticSubstHom g hg hbound hV ⟨X, mem_subring.mpr onOpenDisc_X⟩ =
      ⟨g, mem_subring.mpr hg⟩ :=
  Subtype.ext (X_analyticSubst g)

/-- Substitution is continuous for the topologies of all smaller-radius Gauss norms. -/
@[continuity]
theorem continuous_analyticSubstHom : Continuous (analyticSubstHom g hg hbound hV) := by
  apply TauCeti.PowerSeries.OnOpenDisc.continuous_iff.mpr
  intro s
  have : Fact (0 < (s : ℝ)) := ⟨s.2.1⟩
  obtain ⟨r, hgr, hrU⟩ := exists_between (hbound s s.2.1 s.2.2)
  have hr : 0 < r := (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr
  have : Fact (0 < r) := ⟨hr⟩
  let G : IsRestricted.subring (R := R) (s : ℝ) :=
    ⟨g, (onOpenDisc_iff.mp hg) s s.2.1 s.2.2⟩
  have hG : ‖G‖ ≤ r := hgr.le
  have hcont := (IsRestricted.continuous_evalAtHom
    (fun a ↦ (TauCeti.PowerSeries.norm_algebraMap (s : ℝ) a).le) hG).comp
    (TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_restrict ⟨r, hr, hrU⟩).continuous
  apply hcont.congr
  intro F
  apply Subtype.ext
  simp only [Function.comp_apply, IsRestricted.evalAtHom_apply,
    TauCeti.PowerSeries.OnOpenDisc.coe_restrict, coe_analyticSubstHom]
  rw [TauCeti.PowerSeries.OnOpenDisc.coe_restrict]
  exact (((onOpenDisc_iff.mp (mem_subring.mp F.2)) r hr hrU).analyticSubst_eq_evalAt G.2 hG).symm

end OnOpenDisc

/-- Evaluating an analytic substitution at an interior point is evaluating the outer series
at the value of the inner series. No constant-term vanishing is required. -/
theorem OnOpenDisc.evalAt_analyticSubst (hf : f.OnOpenDisc U) (hg : g.OnOpenDisc V)
    (hbound : ∀ s, 0 < s → s < V → g.gaussNorm norm s < U) {x : R} (hx : ‖x‖ < V) :
    (PowerSeries.analyticSubst f g).evalAt x = f.evalAt (g.evalAt x) := by
  obtain ⟨s, hxs, hsV⟩ := exists_between hx
  have hs : 0 < s := (norm_nonneg x).trans_lt hxs
  have : Fact (0 < s) := ⟨hs⟩
  obtain ⟨r, hgr, hrU⟩ := exists_between (hbound s hs hsV)
  have hr : 0 < r := (gaussNorm_nonneg _ _ _ norm_nonneg).trans_lt hgr
  let G : IsRestricted.subring (R := R) s := ⟨g, (onOpenDisc_iff.mp hg) s hs hsV⟩
  let E : IsRestricted.subring (R := R) s →ₐ[R] R :=
    { IsRestricted.evalAtHom R hxs.le with
      commutes' a := by simp [IsRestricted.evalAtHom_apply] }
  have hE : Continuous E := IsRestricted.continuous_evalAtHom (fun _ ↦ le_rfl) hxs.le
  rw [((onOpenDisc_iff.mp hf) r hr hrU).analyticSubst_eq_evalAt G.2 hgr.le]
  simpa [E, G, IsRestricted.evalAtHom_apply] using
    hf.map_evalAt E hE (show ‖G‖ < U from hbound s hs hsV)

end PowerSeries
