/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.DeGiorgiInterpolation
public import TauCeti.Analysis.GradientFlow.MinimizingMovement
public import TauCeti.Analysis.GradientFlow.MaximalSlope.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Minimizing movements with a lower semicontinuous slope

For a bounded-below lower semicontinuous energy, limits of implicit Euler schemes satisfy
not just an energy–action inequality but the full energy–dissipation inequality, provided
the descending slope is lower semicontinuous. If that slope is a strong upper gradient,
the limit is a curve of maximal slope.

We use De Giorgi's variational interpolation between the discrete nodes. Its distance from
the piecewise constant interpolation tends to zero, and Fatou's lemma then passes the slope
integral to the limit. The selections of intermediate resolvent steps are explicit input;
we require almost-everywhere measurability of their slope integrands, not uniqueness or
continuity of the selections. The theorem does not assert existence of such selections or
compactness of the approximating trajectories. Initial nodes are fixed, so their energies
are automatically well prepared.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Section 2.3 and Theorem 3.2.2.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {φ : X → EReal} {τ : ℕ → ℝ≥0}
  {U : ℕ → ℕ → X} {V : ℕ → ℕ → ℝ → X} {u : ℝ → X} {L S : ℝ}

/-- **The variational interpolation has the same limit as the discrete interpolation.**
For a bounded-below energy and uniformly bounded initial energies, any intermediate
resolvent selections agreeing with the discrete steps at the nodes converge at every
positive time where the piecewise constant interpolants converge. No measurability of
the selections is needed for this pointwise assertion. -/
theorem tendsto_deGiorgiInterpolant_of_forall_mem_moreauYosidaResolvent
    (hL : ∀ x, (L : EReal) ≤ φ x) (hS : ∀ k, φ (U k 0) ≤ S)
    (hτ : ∀ k, 0 < τ k) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n))
    (hV : ∀ k n, ∀ r ∈ Ioc 0 (τ k : ℝ),
      V k n r ∈ moreauYosidaResolvent φ r.toNNReal (U k n))
    (hVU : ∀ k n, V k n (τ k) = U k (n + 1)) {t : ℝ} (ht : 0 < t)
    (hu : Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (𝓝 (u t))) :
    Tendsto (fun k ↦ deGiorgiInterpolant (τ k) (V k) t) atTop (𝓝 (u t)) := by
  have htop k n : φ (U k n) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top S)
    ((antitone_comp_of_forall_mem_moreauYosidaResolvent (hU k) (Nat.zero_le n)).trans (hS k))
  have hbot x : φ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (hL x)
  have hstep k n : dist (U k n) (U k (n + 1)) ≤ Real.sqrt (2 * τ k * (S - L)) := by
    have he := (add_le_add (hL (U k (n + 1)))
      (le_rfl (a := ((edist (U k n) (U k (n + 1)) ^ 2 / (2 * τ k) : ℝ≥0∞) : EReal)))).trans
      ((apply_add_le_of_mem_moreauYosidaResolvent (hU k n)).trans
        ((antitone_comp_of_forall_mem_moreauYosidaResolvent (hU k) (Nat.zero_le n)).trans (hS k)))
    rw [coe_edist_sq_div_eq_coe_dist_sq_div (hτ k), ← EReal.coe_add,
      EReal.coe_le_coe_iff] at he
    apply Real.le_sqrt_of_sq_le
    have hτ' : (0 : ℝ) < τ k := hτ k
    have hp : (0 : ℝ) < 2 * τ k := by positivity
    have hdiv : dist (U k n) (U k (n + 1)) ^ 2 / (2 * τ k) ≤ S - L := by linarith
    have := (div_le_iff₀ hp).1 hdiv
    nlinarith
  have hdist k : dist (deGiorgiInterpolant (τ k) (V k) t) (U k ⌈t / τ k⌉₊) ≤
      2 * Real.sqrt (2 * τ k * (S - L)) := by
    let n := ⌈t / τ k⌉₊ - 1
    have hceil : ⌈t / τ k⌉₊ = n + 1 := by
      have : 1 ≤ ⌈t / τ k⌉₊ := Nat.one_le_ceil_iff.2 (div_pos ht (hτ k))
      omega
    have hmem : t ∈ Ioc (n * τ k : ℝ) ((n + 1) * τ k) := by
      have hc := (Nat.ceil_eq_iff (by omega : n + 1 ≠ 0)).1 hceil
      constructor
      · exact (lt_div_iff₀ (by exact hτ k)).1 (by simpa using hc.1)
      · exact (div_le_iff₀ (by exact hτ k)).1 (by simpa using hc.2)
    have hd := edist_deGiorgiInterpolant_le (hτ k) (hV k n) (hVU k n)
      (htop k n) (hbot _) hmem
    have hd' : dist (U k n) (deGiorgiInterpolant (τ k) (V k) t) ≤
        dist (U k n) (U k (n + 1)) := by
      simpa only [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] using hd
    rw [hceil]
    exact (dist_triangle_left _ _ _).trans (by linarith [hstep k n])
  have hlim : Tendsto (fun k ↦ 2 * Real.sqrt (2 * τ k * (S - L))) atTop (𝓝 0) := by
    have hr := (NNReal.continuous_coe.tendsto 0).comp hτ0
    simpa using ((((hr.const_mul 2).mul_const (S - L)).sqrt).const_mul 2)
  exact (tendsto_iff_of_dist (squeeze_zero (fun _ ↦ dist_nonneg) hdist hlim)).2 hu

end PseudoMetricSpace

variable {X : Type*} [MetricSpace X] {φ : X → EReal} {τ : ℕ → ℝ≥0}
  {U : ℕ → ℕ → X} {V : ℕ → ℕ → ℝ → X} {u : ℝ → X} {L S T : ℝ}

/-- **Lower bound for the slope dissipation.** If the descending slope is lower
semicontinuous on the effective domain, its quadratic integral along a limiting curve
is bounded by the lower limit of the integrals along measurable variational interpolants.
The energy is bounded below and the initial energies are uniformly bounded above. -/
theorem lintegral_descendingSlope_le_liminf_deGiorgiInterpolant
    (hφ : LowerSemicontinuous φ) (hL : ∀ x, (L : EReal) ≤ φ x)
    (hg : LowerSemicontinuousOn (descendingSlope φ) {x | φ x ≠ ⊤})
    (hS : ∀ k, φ (U k 0) ≤ S) (hτ : ∀ k, 0 < τ k) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n))
    (hV : ∀ k n, ∀ r ∈ Ioc 0 (τ k : ℝ),
      V k n r ∈ moreauYosidaResolvent φ r.toNNReal (U k n))
    (hVU : ∀ k n, V k n (τ k) = U k (n + 1)) {T : ℝ}
    (hmeas : ∀ k, AEMeasurable (fun t ↦ descendingSlope φ
      (deGiorgiInterpolant (τ k) (V k) t)) (volume.restrict (Ioc 0 T)))
    (hu : ∀ t ∈ Ioc 0 T, Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (𝓝 (u t))) :
    (∫⁻ t in Ioc 0 T, descendingSlope φ (u t) ^ 2 / 2) ≤
      liminf (fun k ↦ ∫⁻ t in Ioc 0 T,
        descendingSlope φ (deGiorgiInterpolant (τ k) (V k) t) ^ 2 / 2) atTop := by
  refine le_trans (lintegral_mono_ae ?_) (lintegral_liminf_le' fun k ↦
    ((hmeas k).pow_const 2).div_const 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hv := tendsto_deGiorgiInterpolant_of_forall_mem_moreauYosidaResolvent
    hL hS hτ hτ0 hU hV hVU ht.1 (hu t ht)
  have hbound k : φ (deGiorgiInterpolant (τ k) (V k) t) ≤ S :=
    (apply_deGiorgiInterpolant_le_initial (hτ k) (hU k) (hV k) ht.1).trans (hS k)
  have hufin : φ (u t) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EReal.coe_ne_top S) ((hφ.le_liminf _).trans ?_)
    exact hv.liminf_le_liminf_comp.trans (by
      simpa only [Function.comp_def, liminf_const] using
        liminf_le_liminf (f := atTop) (.of_forall hbound))
  have hv' : Tendsto (fun k ↦ deGiorgiInterpolant (τ k) (V k) t) atTop
      (𝓝[{x | φ x ≠ ⊤}] (u t)) :=
    tendsto_nhdsWithin_iff.2 ⟨hv, Eventually.of_forall fun k ↦
      ne_top_of_le_ne_top (EReal.coe_ne_top S) (hbound k)⟩
  have hl := (hg.le_liminf _ hufin).trans hv'.liminf_le_liminf_comp
  have hm : Monotone fun r : ℝ≥0∞ ↦ r ^ 2 / 2 := fun _ _ h ↦
    ENNReal.div_le_div_right (pow_le_pow_left₀ bot_le h 2) _
  exact (hm hl).trans_eq (hm.map_liminf_of_continuousAt _
    ((ENNReal.continuous_div_const 2 (by norm_num)).comp
      (ENNReal.continuous_pow 2)).continuousAt)

/-- **Energy–dissipation inequality for minimizing movements with a lower semicontinuous
slope.** For a bounded-below lower semicontinuous energy, fixed finite-energy initial
nodes and positive time steps tending to zero, pointwise limits of the discrete
interpolants satisfy the quadratic energy–dissipation inequality. The intermediate
resolvent selections must have a.e.-measurable slope integrands. -/
theorem apply_add_dissipation_le_of_forall_mem_moreauYosidaResolvent
    (hφ : LowerSemicontinuous φ) (hL : ∀ x, (L : EReal) ≤ φ x)
    (hg : LowerSemicontinuousOn (descendingSlope φ) {x | φ x ≠ ⊤})
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤)
    (hU0 : ∀ k, U k 0 = x₀) (hτ : ∀ k, 0 < τ k) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n))
    (hV : ∀ k n, ∀ r ∈ Ioc 0 (τ k : ℝ),
      V k n r ∈ moreauYosidaResolvent φ r.toNNReal (U k n))
    (hVU : ∀ k n, V k n (τ k) = U k (n + 1))
    (hmeas : ∀ k, AEMeasurable (fun t ↦ descendingSlope φ
      (deGiorgiInterpolant (τ k) (V k) t)) (volume.restrict (Ioc 0 T)))
    (hu : ∀ t ∈ Icc 0 T, Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (𝓝 (u t))) (hT : 0 ≤ T) :
    φ (u T) + dissipation 2 2 (descendingSlope φ) u 0 T ≤ φ x₀ := by
  set N : ℕ → ℕ := fun k ↦ ⌈T / τ k⌉₊
  set P : ℕ → ℝ≥0∞ := fun k ↦ ∑ n ∈ Finset.range (N k),
    edist (U k n) (U k (n + 1)) ^ 2 / (2 * τ k)
  set G : ℕ → ℝ≥0∞ := fun k ↦ ∫⁻ t in Ioc 0 T,
    descendingSlope φ (deGiorgiInterpolant (τ k) (V k) t) ^ 2 / 2
  have hS k : φ (U k 0) ≤ (φ x₀).toReal := by
    rw [hU0 k, EReal.coe_toReal hx₀ (ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (hL x₀))]
  -- Pass the terminal energy, discrete action and slope integral to the limit separately.
  have hE : φ (u T) ≤ liminf (fun k ↦ φ (U k (N k))) atTop :=
    (hφ.le_liminf _).trans (hu T ⟨hT, le_rfl⟩).liminf_le_liminf_comp
  have hA : curveAction 2 u 0 T / 2 ≤ liminf P atTop := by
    have h := curveAction_le_liminf_sum_edist_rpow (l := atTop) one_lt_two
      (.of_forall hτ) hτ0 hT (fun s hs t ht ↦ ((hu s hs).edist (hu t ht)).liminf_eq.ge)
    have heq (d : ℝ≥0∞) (r : ℝ≥0) :
        d ^ (2 : ℝ) / (r : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 * (d ^ 2 / (2 * r)) := by
      rw [ENNReal.rpow_two, (by norm_num : (2 : ℝ) - 1 = 1), ENNReal.rpow_one,
        ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ two_ne_zero ENNReal.ofNat_ne_top]
    simp only [heq, ← Finset.mul_sum] at h
    rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofNat_ne_top] at h
    exact ENNReal.div_le_of_le_mul' h
  have hG : (∫⁻ t in Ioc 0 T, descendingSlope φ (u t) ^ 2 / 2) ≤ liminf G atTop :=
    lintegral_descendingSlope_le_liminf_deGiorgiInterpolant hφ hL hg hS hτ hτ0 hU hV hVU hmeas
      (fun t ht ↦ hu t ⟨ht.1.le, ht.2⟩)
  -- The final discrete interval may overshoot `T`; its nonnegative integral can be discarded.
  have hdisc k : φ (U k (N k)) + (P k : EReal) + (G k : EReal) ≤ φ x₀ := by
    have h := apply_add_sum_add_lintegral_descendingSlope_le_of_forall_mem_moreauYosidaResolvent
      (hτ k) (hU k) (hV k) (N k)
    rw [hU0 k] at h
    refine le_trans (add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.2 ?_)) h
    apply lintegral_mono_set
    exact Ioc_subset_Ioc_right ((div_le_iff₀ (by exact hτ k)).1 (Nat.le_ceil _))
  -- Add the three lower bounds in `EReal`, keeping possible infinite dissipations.
  have hcast (f : ℕ → ℝ≥0∞) : (↑(liminf f atTop) : EReal) =
      liminf (fun k ↦ (f k : EReal)) atTop :=
    EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt _
      continuous_coe_ennreal_ereal.continuousAt
  have hGI : (∫⁻ t in Ι (0 : ℝ) T, descendingSlope φ (u t) ^ 2) / 2 =
      ∫⁻ t in Ioc 0 T, descendingSlope φ (u t) ^ 2 / 2 := by
    rw [uIoc_of_le hT]
    simp only [div_eq_mul_inv]
    exact (lintegral_mul_const' _ _ (by norm_num)).symm
  simp only [dissipation_def, ENNReal.ofReal_ofNat, ENNReal.rpow_two, hGI,
    EReal.coe_ennreal_add, ← add_assoc]
  calc φ (u T) + ((curveAction 2 u 0 T / 2 : ℝ≥0∞) : EReal) +
        ((∫⁻ t in Ioc 0 T, descendingSlope φ (u t) ^ 2 / 2 : ℝ≥0∞) : EReal)
      ≤ liminf (fun k ↦ φ (U k (N k))) atTop + liminf (fun k ↦ (P k : EReal)) atTop +
          liminf (fun k ↦ (G k : EReal)) atTop := by
        exact add_le_add (add_le_add hE
          ((EReal.coe_ennreal_le_coe_ennreal_iff.2 hA).trans_eq (hcast P)))
          ((EReal.coe_ennreal_le_coe_ennreal_iff.2 hG).trans_eq (hcast G))
    _ ≤ liminf (fun k ↦ φ (U k (N k)) + (P k : EReal) + (G k : EReal)) atTop :=
      (add_le_add EReal.le_liminf_add le_rfl).trans EReal.le_liminf_add
    _ ≤ φ x₀ := by simpa using liminf_le_liminf (f := atTop) (.of_forall hdisc)

/-- **Limits of minimizing movements are curves of maximal slope.** For a bounded-below
lower semicontinuous energy whose descending slope is lower semicontinuous and a strong
upper gradient, every pointwise limit on `[0,T]` of implicit Euler interpolants started
at a fixed finite-energy point is a curve of maximal slope, provided intermediate
resolvent selections with a.e.-measurable slope integrands are supplied. -/
theorem isCurveOfMaximalSlope_of_forall_mem_moreauYosidaResolvent
    (hφ : LowerSemicontinuous φ) (hL : ∀ x, (L : EReal) ≤ φ x)
    (hg : LowerSemicontinuousOn (descendingSlope φ) {x | φ x ≠ ⊤})
    (hstrong : IsStrongUpperGradient φ (descendingSlope φ))
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) (hU0 : ∀ k, U k 0 = x₀)
    (hτ : ∀ k, 0 < τ k) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n))
    (hV : ∀ k n, ∀ r ∈ Ioc 0 (τ k : ℝ),
      V k n r ∈ moreauYosidaResolvent φ r.toNNReal (U k n))
    (hVU : ∀ k n, V k n (τ k) = U k (n + 1))
    (hmeas : ∀ k, AEMeasurable (fun t ↦ descendingSlope φ
      (deGiorgiInterpolant (τ k) (V k) t)) (volume.restrict (Ioc 0 T)))
    (hu : ∀ t ∈ Icc 0 T, Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (𝓝 (u t))) (hT : 0 ≤ T) :
    IsCurveOfMaximalSlope 2 2 φ (descendingSlope φ) u (Icc 0 T) := by
  have hbot x : φ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (hL x)
  have hcoer : moreauYosida φ 1 x₀ ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (le_moreauYosida_iff.2 fun y _ ↦ ?_)
    exact (hL y).trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
  have hS k : φ (U k 0) ≤ (φ x₀).toReal := by
    rw [hU0 k, EReal.coe_toReal hx₀ (hbot x₀)]
  have hAC := absolutelyContinuousOnInterval_of_forall_mem_moreauYosidaResolvent
    (l := 𝓝) (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge)
    zero_lt_one hcoer hτ hτ0 hU (by simpa only [hU0] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x₀) atTop (𝓝 x₀))) hS hu hT
  have hu0 : u 0 = x₀ := by
    have h := hu 0 ⟨le_rfl, hT⟩
    simp only [zero_div, Nat.ceil_zero, hU0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine (isCurveOfMaximalSlope_Icc_iff hstrong Real.HolderConjugate.two_two hT hAC).2
    ⟨hu0 ▸ hx₀, hbot _, ?_⟩
  rw [hu0]
  exact apply_add_dissipation_le_of_forall_mem_moreauYosidaResolvent
    hφ hL hg hx₀ hU0 hτ hτ0 hU hV hVU hmeas hu hT

end TauCeti
