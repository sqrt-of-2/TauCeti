/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
public import TauCeti.RingTheory.Perfectoid.PerfectRing

/-!
# When the tilt of a uniform Tate ring is Tate

The integral tilt of a ring of integral elements is open and bounded for the inverse-limit
topology. Units and topological nilpotence can be tested on the zeroth coordinate. Consequently,
if a compatible system of roots has a pseudouniformiser as zeroth coordinate, the tilt is a Tate
ring. Since it is perfect of characteristic `p`, it is then perfectoid. No perfectoidness of the
original ring is needed, nor any divisibility condition on the pseudouniformiser.

This supplies the Tate-ring structure needed to use the integral tilt as a ring of definition.
It also identifies the power-bounded elements of the tilt by their zeroth coordinates.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemma 2.7.1(a), (c).
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [hp : Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-- The integral tilt is an open subring: membership is tested on the zeroth coordinate. -/
theorem isOpen_plusSubring {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) :
    IsOpen (plusSubring p h : Set (uniformTilt p B)) := by
  have he : (plusSubring p h : Set (uniformTilt p B)) = coeff p B 0 ⁻¹' Bplus :=
    Set.ext fun _ ↦ mem_plusSubring_iff_coeff_zero
  rw [he]
  exact h.isOpen.preimage (continuous_coeff 0)

/-- The integral tilt is bounded, because each coordinate lies in the bounded ring `B°`. -/
theorem isBounded_plusSubring {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) :
    IsBounded (plusSubring p h : Set (uniformTilt p B)) := by
  rw [Huber.isBounded_iff]
  intro U hU
  rw [isEmbedding_coeff.isInducing.nhds_eq_comap] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  simp only [coeff_zero, nhds_pi] at hW
  obtain ⟨s, hs, V, hV, hVW⟩ := Filter.mem_pi.mp hW
  choose T hT hTV using fun n ↦
    Huber.isBounded_iff.mp IsUniform.isBounded_powerBoundedSubring (V n) (hV n)
  refine ⟨⋂ n ∈ s, coeff p B n ⁻¹' T n, ?_, ?_⟩
  · exact (Filter.biInter_mem hs).mpr fun n _ ↦
      (continuous_coeff n).continuousAt.preimage_mem_nhds (by simpa using hT n)
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    apply hWU
    apply hVW
    intro n hn
    dsimp only
    rw [map_mul]
    exact hTV n (Set.mul_mem_mul (Set.mem_iInter₂.mp hx n hn)
      (h.le_powerBoundedSubring (mem_plusSubring_iff.mp hy n)))

/-- Topological nilpotence in the tilt is detected by the zeroth coordinate. -/
@[simp]
theorem isTopologicallyNilpotent_iff_coeff_zero {x : uniformTilt p B} :
    IsTopologicallyNilpotent x ↔ IsTopologicallyNilpotent (coeff p B 0 x) := by
  constructor
  · intro hx
    simpa only [IsTopologicallyNilpotent, Function.comp_def, map_pow, coeff_zero] using
      (continuous_coeff 0).continuousAt.tendsto.comp hx
  · intro hx
    apply tendsto_nhds_iff.mpr
    intro n
    simp only [map_pow, coeff_zero]
    apply IsTopologicallyNilpotent.of_pow (pow_ne_zero n hp.out.ne_zero)
    simpa only [← coeff_pow_p_pow x 0 n, zero_add] using hx

/-- An element of the tilt is a unit exactly when its zeroth coordinate is a unit. -/
@[simp]
theorem isUnit_iff_coeff_zero {x : uniformTilt p B} :
    IsUnit x ↔ IsUnit (coeff p B 0 x) := by
  refine ⟨fun hx ↦ hx.map _, fun hx ↦ ?_⟩
  have hu (n : ℕ) : IsUnit (coeff p B n x) := by
    apply (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).mp
    simpa only [← coeff_pow_p_pow x 0 n, zero_add] using hx
  let u (n : ℕ) : Bˣ := (hu n).unit
  have hpow (n : ℕ) : u (n + 1) ^ p = u n := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, u, IsUnit.unit_spec] using coeff_pow_p x n
  let y : uniformTilt p B := mk (fun n ↦ ↑((u n)⁻¹)) (fun n ↦ by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hpow])
  refine isUnit_iff_exists_inv.mpr ⟨y, ext fun n ↦ ?_⟩
  simp only [map_mul, y, coeff_mk, map_one]
  exact (hu n).mul_val_inv

/-- A compatible system whose zeroth coordinate is a pseudouniformiser makes the tilt Tate. -/
theorem isTateRing_of_sharp {ϖ : uniformTilt p B}
    (hϖ : IsPseudoUniformizer (coeff p B 0 ϖ)) : IsTateRing (uniformTilt p B) :=
  IsTateRing.of_isOpen_isBounded
    (plusSubring p (isRingOfIntegralElements_powerBoundedSubring B))
    (isOpen_plusSubring _) (isBounded_plusSubring _)
    (isPseudoUniformizer_iff.mpr ⟨isUnit_iff_coeff_zero.mpr hϖ.isUnit,
      isTopologicallyNilpotent_iff_coeff_zero.mpr hϖ.isTopologicallyNilpotent⟩)

/-- Under the compatible-pseudouniformiser hypothesis, power-boundedness in the tilt is detected
by the zeroth coordinate. -/
theorem mem_powerBoundedSubring_iff {ϖ : uniformTilt p B}
    (hϖ : IsPseudoUniformizer (coeff p B 0 ϖ)) {x : uniformTilt p B} :
    letI := isTateRing_of_sharp hϖ
    x ∈ powerBoundedSubring (uniformTilt p B) ↔ coeff p B 0 x ∈ powerBoundedSubring B := by
  let := isTateRing_of_sharp hϖ
  let hB := isRingOfIntegralElements_powerBoundedSubring B
  constructor
  · intro hx
    have hnil : IsTopologicallyNilpotent ϖ :=
      isTopologicallyNilpotent_iff_coeff_zero.mpr hϖ.isTopologicallyNilpotent
    obtain ⟨N, hN⟩ := (isPowerBounded_iff.mp (mem_powerBoundedSubring.mp hx)).exists_pow_mul_subset
      hnil ((isOpen_plusSubring hB).mem_nhds (zero_mem _))
    have hpow (n : ℕ) : coeff p B 0 ϖ ^ N * coeff p B 0 x ^ n ∈ powerBoundedSubring B := by
      have := mem_plusSubring_iff_coeff_zero.mp
        (hN (Set.mul_mem_mul (Set.mem_singleton _) (Set.mem_range_self n)))
      simpa only [map_mul, map_pow] using this
    let u := (hϖ.isUnit.pow N).unit
    apply mem_powerBoundedSubring.mpr
    apply isPowerBounded_iff.mpr
    apply ((isBounded_singleton (↑u⁻¹ : B)).mul IsUniform.isBounded_powerBoundedSubring).subset
    rintro _ ⟨n, rfl⟩
    exact Set.mem_mul.mpr ⟨_, rfl, _, hpow n, (hϖ.isUnit.pow N).unit.inv_mul_cancel_left _⟩
  · intro hx
    exact mem_powerBoundedSubring.mpr ((isBounded_plusSubring hB).isPowerBounded_of_mem
      (mem_plusSubring_iff_coeff_zero.mpr hx))

/-- A tilt containing a compatible pseudouniformiser is perfectoid, even if the original complete
uniform Tate ring is not perfectoid. The zero ring is included. -/
theorem isPerfectoidTateRing_of_sharp {ϖ : uniformTilt p B}
    (hϖ : IsPseudoUniformizer (coeff p B 0 ϖ)) :
    letI := isTateRing_of_sharp hϖ
    IsPerfectoidTateRing p (uniformTilt p B) := by
  let := isTateRing_of_sharp hϖ
  rcases subsingleton_or_nontrivial B with hB | hB
  · let := hB
    have : Subsingleton (uniformTilt p B) := ⟨fun _ _ ↦ ext fun _ ↦ Subsingleton.elim _ _⟩
    exact isPerfectoidTateRing_of_subsingleton p _
  · let := hB
    exact IsPerfectoidTateRing.of_perfectRing

end TauCeti.Perfectoid.uniformTilt
