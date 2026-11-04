/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Evaluating cyclotomic polynomials at primitive roots

A primitive `e`-th root of unity in a domain is a root of the cyclotomic polynomial `Φ_e` over any
ring, once its coefficients are mapped into the domain along a ring homomorphism.

Coprime powers preserve cyclotomic roots even without invertibility of `n`
(`Polynomial.isRoot_cyclotomic_pow_of_coprime`).
-/

public section

open Polynomial

namespace IsPrimitiveRoot

/-- A primitive `e`-th root of unity `r` in a domain `R` is a root of the cyclotomic polynomial
`Φ_e` over any ring, mapped to `R` along any ring homomorphism `f`. Mathlib's
`IsPrimitiveRoot.isRoot_cyclotomic` is the case of `Φ_e` taken over `R` itself. -/
theorem eval₂_cyclotomic {e : ℕ} {S R : Type*} [Ring S] [CommRing R] [IsDomain R] [NeZero e]
    (f : S →+* R) {r : R} (hr : IsPrimitiveRoot r e) : (cyclotomic e S).eval₂ f r = 0 := by
  rw [← eval_map, map_cyclotomic]
  exact hr.isRoot_cyclotomic (NeZero.pos e)

end IsPrimitiveRoot

namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- If `a` is coprime to `n`, then `Φ_n(X)` divides `Φ_n(X ^ a)` over any
commutative ring. -/
theorem cyclotomic_dvd_comp_X_pow_of_coprime {a : ℕ} (ha : a.Coprime n) :
    cyclotomic n R ∣ (cyclotomic n R).comp (X ^ a) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  -- Use Φ_n = minpoly ℤ (exp(2πi/n)); this root also annihilates Φ_n(X^a).
  have hp := Complex.isPrimitiveRoot_exp n hn.ne'
  have hd := minpoly.isIntegrallyClosed_dvd (hp.isIntegral hn)
    (p := (cyclotomic n ℤ).comp (X ^ a)) (by
    rw [aeval_comp]
    simpa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] using
      ((hp.pow_of_coprime a ha).isRoot_cyclotomic hn).eq_zero)
  rw [← cyclotomic_eq_minpoly hp hn] at hd
  simpa only [map_comp, Polynomial.map_pow, map_X, map_cyclotomic_int] using
    Polynomial.map_dvd (Int.castRingHom R) hd

/-- A power of a cyclotomic root with exponent coprime to `n` is again a cyclotomic
root over any commutative ring, including in ramified characteristics. -/
theorem isRoot_cyclotomic_pow_of_coprime {ζ : R}
    (hζ : (cyclotomic n R).IsRoot ζ) {a : ℕ} (ha : a.Coprime n) :
    (cyclotomic n R).IsRoot (ζ ^ a) := by
  simpa only [isRoot_comp, eval_pow, eval_X] using
    hζ.dvd (cyclotomic_dvd_comp_X_pow_of_coprime ha)

end Polynomial
