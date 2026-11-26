/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Newman
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ResidueClass
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.ResidueClass

/-!
# The constant term of the signed prime sum

For an odd prime `d` coprime to the progression modulus `q`, the signed prime remainder
`R_q(y)` tends to zero. In particular, the real part of `G_q(1)` used to define the remainder
is the actual constant term of the normalized smoothed sum. This limit uses Newman's
Tauberian theorem and does not require a prime number theorem with a rate.

For the signed normalization see `lsernau/grh-lean`, revision `72fead1`,
`grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean` (`New.tendsto_primeRemainder`).
-/

public section

open ArithmeticFunction DirichletCharacter Filter
open scoped Topology

namespace TauCeti.OneSidedBound

/-- Identify the signed normalization at the endpoint using the least-common-multiple
form of the twisted residue-class series. -/
private theorem logDerivMean_one_eq_residueClass_sub_twist {d q : ℕ}
    [Fact d.Prime] [NeZero d] [NeZero q]
    (hne : ∀ ψ : DirichletCharacter ℂ q,
      ψ.mul ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) ≠ 1) :
    let ξ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
    logDerivMean d q 1 = vonMangoldt.LFunctionResidueClassAux (1 : ZMod q) 1 -
      vonMangoldt.LFunctionTwistResidueClass (1 : ZMod q) ξ 1 - (q.totient : ℂ)⁻¹ := by
  intro ξ
  let _ : NeZero (q * d) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne d)⟩
  let hlevel : q.lcm d ∣ q * d := Nat.lcm_dvd (dvd_mul_right q d) (dvd_mul_left d q)
  have hL (ψ : DirichletCharacter ℂ q) : (quadraticTwist d ψ).entireLFunction =
      (ψ.mul ξ).LFunction := by
    have hTw : changeLevel hlevel (ψ.mul ξ) = quadraticTwist d ψ := by
      simp [DirichletCharacter.mul, quadraticTwist_def, ξ, ← changeLevel_trans]
    have hne' : quadraticTwist d ψ ≠ 1 := fun h ↦
      hne ψ ((changeLevel_eq_one_iff hlevel).mp (hTw.trans h))
    rw [entireLFunction_of_ne_one hne', ← hTw]
    ext s
    rw [LFunction_changeLevel hlevel _ (.inl (hne ψ))]
    -- The two levels have the same prime divisors, so no Euler factor is removed.
    suffices (∏ p ∈ (q * d).primeFactors, (1 - ψ.mul ξ p * (p : ℂ) ^ (-s))) = 1 by
      rw [this, mul_one]
    refine Finset.prod_eq_one fun p hp ↦ ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ q.lcm d :=
      (hp'.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp)).elim
        (fun h ↦ h.trans (Nat.dvd_lcm_left ..)) (fun h ↦ h.trans (Nat.dvd_lcm_right ..))
    have hp₀ : ¬ IsUnit (p : ZMod (q.lcm d)) := fun hu ↦
      (hp'.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime ..).mp hu)) hpd
    simp [(ψ.mul ξ).map_nonunit hp₀]
  rw [logDerivMean_def, Finset.sum_sub_distrib,
    vonMangoldt.LFunctionResidueClassAux_one_eq_neg_mean_logDeriv]
  simp [vonMangoldt.LFunctionTwistResidueClass_def, hL, div_eq_mul_inv]
  ring

/-- At a nonzero modulus coprime to the odd prime `d`, the signed prime remainder tends to
zero as the real cutoff tends to infinity. -/
theorem tendsto_primeRemainder (d q : ℕ) [Fact d.Prime] [NeZero q]
    (hd : d ≠ 2) (hq : q.Coprime d) : Tendsto (primeRemainder d q) atTop (𝓝 0) := by
  classical
  let _ : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
  let ξ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  let A : ℂ := (q.totient : ℂ)⁻¹
  let F (s : ℂ) := vonMangoldt.LFunctionResidueClassAux (1 : ZMod q) s -
    vonMangoldt.LFunctionTwistResidueClass (1 : ZMod q) ξ s - A
  have hcξ : ξ.conductor = d := by
    simpa [ξ] using conductor_changeLevel_quadraticChar (R := ℂ) (p := d)
      (by simp [ringChar.eq_zero]) hd (dvd_refl d)
  have hne (ψ : DirichletCharacter ℂ q) : ψ.mul ξ ≠ 1 := fun h ↦
    ((Fact.out : d.Prime).coprime_iff_not_dvd.mp hq.symm)
      (hcξ ▸ (ξ.exists_mul_eq_one_iff_conductor_dvd (q := q)).mp ⟨ψ, h⟩)
  have hF (s : ℂ) (hs : s.re = 1) : AnalyticAt ℂ F s := by
    have hB := vonMangoldt.analyticAt_LFunctionResidueClassAux_of_one_le_re (1 : ZMod q) hs.ge
    have hTw := vonMangoldt.analyticAt_LFunctionTwistResidueClass (1 : ZMod q) ξ (s := s) fun ψ ↦
      ⟨(ψ.mul ξ).analyticAt_LFunction (.inr (hne ψ)),
        (ψ.mul ξ).LFunction_ne_zero_of_one_le_re (.inl (hne ψ)) hs.ge⟩
    exact (hB.sub hTw).sub analyticAt_const
  have hseries (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (primeWeight d q n : ℂ)) s (F s + A * s / (s - 1)) := by
    have h := vonMangoldt.LSeriesHasSum_residueClass_mul_one_sub (isUnit_one (M := ZMod q)) ξ hs
    rw [← LSeriesHasSum_congr (f := fun n ↦ (primeWeight d q n : ℂ)) s _ (fun {n} _ ↦ by
      simp only [primeWeight_def, vonMangoldt.residueClass, Set.indicator_apply,
        Set.mem_ofPred_eq, legendreSym, ξ]
      split_ifs <;> simp [MulChar.ringHomComp_apply])] at h
    convert h using 1
    simp only [F, A, vonMangoldt.LFunctionTwistResidueClass_def, div_eq_mul_inv, mul_inv_rev]
    ring
  have hlim := tendsto_rieszSum_div_sub_log_of_analyticAt (M := 2 * (Real.log 4 + 4))
    (a := fun n ↦ (primeWeight d q n : ℂ)) (A := A) (fun x hx ↦ by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
        (Finset.sum_nonneg fun n _ ↦ primeWeight_nonneg d q n)]
      exact sum_primeWeight_le d q (zero_le_one.trans hx)) hF hseries
  have hconst : logDerivMean d q 1 = F 1 := logDerivMean_one_eq_residueClass_sub_twist hne
  rw [← hconst] at hlim
  have hr := ((Complex.continuous_re.tendsto _).comp hlim).sub_const (logDerivMean d q 1).re
  rw [sub_self] at hr
  refine hr.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hy₀ : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hy).ne'
  simp only [primeRemainder_def, Function.comp_apply, rieszSum_def, Finset.sum_div,
    Complex.sub_re, Complex.re_sum]
  congr 2
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn₀ : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    have he : (primeWeight d q n : ℂ) * ((y : ℂ) / n - 1) / y =
        (primeWeight d q n : ℂ) * (1 / n - 1 / y) := by field_simp
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div,
      ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re] using congrArg Complex.re he
  · simp [A, div_eq_mul_inv, mul_comm, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul]

end TauCeti.OneSidedBound
