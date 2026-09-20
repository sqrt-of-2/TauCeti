/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Rigidity of the pre-Schwarzian derivative

The **pre-Schwarzian derivative** of a holomorphic function `f` is `logDeriv (deriv f) = f'' / f'`.
Postcomposing `f` with `w ↦ a * w + b` for `a ≠ 0` leaves it unchanged, and this file proves the
converse: on a domain -- an open preconnected subset of `ℂ` -- two holomorphic functions with
nonvanishing derivatives and the same pre-Schwarzian derivative differ by exactly such a
postcomposition.

This is the statement that integrates a pre-Schwarzian differential equation, such as the
Schwarz--Christoffel equation `f'' / f' = ∑ i, e i / (z - a i)`, back to its solutions.

## Main results

* `TauCeti.logDeriv_deriv_const_mul_add_const` -- postcomposition with `w ↦ a * w + b` for
  `a ≠ 0` leaves the pre-Schwarzian derivative unchanged.
* `TauCeti.exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn` -- two holomorphic functions with
  nonvanishing derivatives on a domain have the same pre-Schwarzian derivative exactly when one
  is `w ↦ a * w + b` applied to the other, for some `a ≠ 0`.
* `TauCeti.eqOn_const_mul_sub_add_of_logDeriv_deriv_eqOn` -- the same conclusion with the two
  constants read off from the values and the derivatives at a base point.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

namespace TauCeti

open Set

/-- **Affine invariance of the pre-Schwarzian derivative.** Postcomposing a function with
`w ↦ a * w + b` for a nonzero constant `a` leaves `logDeriv (deriv ·)` unchanged. -/
theorem logDeriv_deriv_const_mul_add_const {a : ℂ} (ha : a ≠ 0) (b : ℂ) (g : ℂ → ℂ) :
    logDeriv (deriv fun z => a * g z + b) = logDeriv (deriv g) := by
  rw [deriv_add_const', deriv_const_mul_field']
  exact funext fun z => logDeriv_const_mul z a ha

/-- **Rigidity of the pre-Schwarzian derivative.** Two holomorphic functions with nonvanishing
derivatives on a domain have equal pre-Schwarzian derivatives exactly when one is obtained from
the other by postcomposition with `w ↦ a * w + b` for a nonzero constant `a`. -/
theorem exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconn : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfn : ∀ z ∈ Ω, deriv f z ≠ 0) (hgn : ∀ z ∈ Ω, deriv g z ≠ 0) :
    (∃ a : ℂ, a ≠ 0 ∧ ∃ b : ℂ, EqOn f (fun z => a * g z + b) Ω) ↔
      EqOn (logDeriv (deriv f)) (logDeriv (deriv g)) Ω := by
  constructor
  · rintro ⟨a, ha, b, hfg⟩ z hz
    have hev : f =ᶠ[nhds z] fun w => a * g w + b :=
      Filter.eventuallyEq_of_mem (hΩopen.mem_nhds hz) hfg
    rw [(logDeriv_congr_nhds hev.deriv).eq_of_nhds, logDeriv_deriv_const_mul_add_const ha]
  · rw [logDeriv_eqOn_iff (hf.deriv hΩopen) (hg.deriv hΩopen) hΩopen hΩconn hgn hfn]
    rintro ⟨a, ha, hderiv⟩
    refine ⟨a, ha, ?_⟩
    have hag : DifferentiableOn ℂ (fun z => a * g z) Ω :=
      fun z hz => (hg z hz).const_mul a
    obtain ⟨b, hb⟩ := hΩopen.exists_eq_add_of_deriv_eq hΩconn hf hag fun z hz => by
      simpa [deriv_const_mul_field] using hderiv hz
    exact ⟨b, hb⟩

/-- **Normalized rigidity of the pre-Schwarzian derivative.** Two holomorphic functions with
nonvanishing derivatives and equal pre-Schwarzian derivatives on a domain are related by the
affine map whose constants are read off at any base point `z₀` of the domain:

`f z = (f'(z₀) / g'(z₀)) * (g z - g z₀) + f z₀`. -/
theorem eqOn_const_mul_sub_add_of_logDeriv_deriv_eqOn {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconn : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfn : ∀ z ∈ Ω, deriv f z ≠ 0) (hgn : ∀ z ∈ Ω, deriv g z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hpre : EqOn (logDeriv (deriv f)) (logDeriv (deriv g)) Ω) :
    EqOn f (fun z => deriv f z₀ / deriv g z₀ * (g z - g z₀) + f z₀) Ω := by
  obtain ⟨a, _, b, hEq⟩ :=
    (exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn hΩopen hΩconn hf hg hfn hgn).mpr hpre
  have hderiv := hEq.deriv hΩopen hz₀
  have ha : deriv f z₀ / deriv g z₀ = a := by
    rw [deriv_add_const, deriv_const_mul_field] at hderiv
    exact div_eq_of_eq_mul (hgn z₀ hz₀) hderiv
  intro z hz
  rw [hEq hz, ha, hEq hz₀]
  ring

end TauCeti
