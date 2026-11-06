/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Independence
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Fundamental cycle bases from spanning forests

Restriction to the chords of a spanning forest identifies the incidence kernel with the
finitely supported chord coordinates, over any ring. Its inverse supplies the fundamental
cycles: a chord traversed forward, closed by a signed chain in the forest. Every cycle has
a unique finite expansion whose coefficients are its own chord coordinates.

In particular this constructs integral and binary cycle bases using the same forest. Loops
and parallel edges retain their individual coordinates. No finiteness, connectedness,
nonemptiness or orientation hypothesis is needed. The kernel is free, and is finite free when
the chosen dart set is finite. Over a ring satisfying the strong rank condition, a finite
graph's cycle rank plus its vertex count equals its chosen dart count plus its component count.

## References

* R. Diestel, *Graph Theory*, §1.9, Theorem 1.9.6 (fundamental cycle bases).
* A. Hatcher, *Algebraic Topology*, §2.2 (signed incidence and coefficients).
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {O F : Set Γ.E} {R : Type*} [Ring R]

/-- Every chord has a cycle with its unit chord coordinate and zero at all other chords.
The correction to the chord is supported on the forest. -/
private theorem IsSpanningForest.exists_cycle_single_chord (hF : Γ.IsSpanningForest O F)
    (e : ↥(O \ F)) :
    ∃ c : (Γ.incidenceBoundary O R).ker,
      ∀ f : ↥(O \ F), c.val ⟨f.val, f.property.1⟩ =
        (Finsupp.single e 1 : ↥(O \ F) →₀ R) f := by
  classical
  have hr : (Γ.supportGraph O).Reachable (Γ.src e.val) (Γ.tgt e.val) := by
    by_cases h : Γ.src e.val = Γ.tgt e.val
    · exact h ▸ SimpleGraph.Reachable.refl _
    · exact ((Γ.supportGraph_adj O _ _).mpr
        ⟨h, Or.inl ⟨e.val, e.property.1, rfl, rfl⟩⟩).reachable
  obtain ⟨p, hp⟩ := exists_incidenceBoundary_eq_sub_of_reachable
    (R := R) (hF.reachable_eq ▸ hr)
  let c : O →₀ R := Finsupp.single ⟨e.val, e.property.1⟩ 1 -
    Finsupp.mapDomain (Set.inclusion hF.subset) p
  have hc : Γ.incidenceBoundary O R c = 0 := by
    simp [c, incidenceBoundary_mapDomain_inclusion, hp]
  refine ⟨⟨c, hc⟩, fun f => ?_⟩
  have hzero : Finsupp.mapDomain (Set.inclusion hF.subset) p
      ⟨f.val, f.property.1⟩ = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨g, hg⟩
    exact f.property.2 (congrArg Subtype.val hg ▸ g.property)
  simp only [c, Finsupp.sub_apply, hzero, sub_zero, Finsupp.single_apply]
  congr 1
  exact propext (by simp only [Subtype.ext_iff])

/-- Chord coordinates give a linear equivalence from cycles to finite chord families.
Thus every prescribed finite family of chord coefficients extends uniquely to a cycle. -/
noncomputable def IsSpanningForest.cycleEquivChords (hF : Γ.IsSpanningForest O F)
    (R : Type*) [Ring R] :
    (Γ.incidenceBoundary O R).ker ≃ₗ[R] (↥(O \ F) →₀ R) := by
  let i : ↥(O \ F) → O := Set.inclusion Set.sdiff_subset
  let res := (Finsupp.lcomapDomain i (Set.inclusion_injective _)).comp
    (Γ.incidenceBoundary O R).ker.subtype
  apply LinearEquiv.ofBijective res
  constructor
  · intro c d h
    apply Subtype.ext
    apply hF.eq_of_incidenceBoundary_eq_of_forall_notMem c.val d.val
      (c.property.trans d.property.symm)
    intro e he
    exact congrArg (fun x : ↥(O \ F) →₀ R => x ⟨e.val, e.property, he⟩) h
  · intro x
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0, map_zero res⟩
    | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [map_add, hc, hd]⟩
    | single e r =>
      obtain ⟨c, hc⟩ := hF.exists_cycle_single_chord (R := R) e
      refine ⟨r • c, ?_⟩
      have hres : res c = Finsupp.single e 1 := by
        ext f
        exact hc f
      rw [map_smul, hres, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The cycle/chord equivalence reads the original edge coordinate at each chord. -/
@[simp] theorem IsSpanningForest.cycleEquivChords_apply (hF : Γ.IsSpanningForest O F)
    (c : (Γ.incidenceBoundary O R).ker) (e : ↥(O \ F)) :
    hF.cycleEquivChords R c e = c.val ⟨e.val, e.property.1⟩ := by
  rfl

/-- Reconstructing a cycle from chord coordinates preserves those coordinates. -/
@[simp] theorem IsSpanningForest.cycleEquivChords_symm_apply
    (hF : Γ.IsSpanningForest O F) (x : ↥(O \ F) →₀ R) (e : ↥(O \ F)) :
    ((hF.cycleEquivChords R).symm x).val ⟨e.val, e.property.1⟩ = x e := by
  rw [← hF.cycleEquivChords_apply, LinearEquiv.apply_symm_apply]

/-- The fundamental cycle basis indexed by the actual chords. Specializing to `ℤ` gives
an integral cycle-lattice basis, and specializing to `ZMod 2` gives a binary cycle basis. -/
noncomputable def IsSpanningForest.cycleBasis (hF : Γ.IsSpanningForest O F)
    (R : Type*) [Ring R] :
    Module.Basis ↥(O \ F) R (Γ.incidenceBoundary O R).ker :=
  Module.Basis.ofRepr (hF.cycleEquivChords R)

/-- The coefficient of a fundamental cycle in any cycle is that cycle's chord coordinate. -/
@[simp] theorem IsSpanningForest.cycleBasis_repr_apply (hF : Γ.IsSpanningForest O F)
    (c : (Γ.incidenceBoundary O R).ker) (e : ↥(O \ F)) :
    (hF.cycleBasis R).repr c e = c.val ⟨e.val, e.property.1⟩ := by
  exact hF.cycleEquivChords_apply c e

/-- Fundamental cycles have unit chord coordinates. This characterizes each basis cycle
uniquely among all cycles, even for loops or parallel edges. -/
@[simp] theorem IsSpanningForest.cycleBasis_apply_chord (hF : Γ.IsSpanningForest O F)
    (e f : ↥(O \ F)) :
    ((hF.cycleBasis R) e).val ⟨f.val, f.property.1⟩ =
      (Finsupp.single e 1 : ↥(O \ F) →₀ R) f := by
  rw [← hF.cycleBasis_repr_apply, Module.Basis.repr_self]

/-- The incidence kernel is free over every ring, even for an infinite multigraph. -/
instance instFreeKerIncidenceBoundary : Module.Free R (Γ.incidenceBoundary O R).ker := by
  obtain ⟨F, hF⟩ := Γ.exists_spanningForest O
  exact Module.Free.of_basis (hF.cycleBasis R)

/-- Finitely many actual edges give a finite free cycle module; the vertex type can be infinite. -/
instance instFiniteKerIncidenceBoundary [Finite O] :
    Module.Finite R (Γ.incidenceBoundary O R).ker := by
  obtain ⟨F, hF⟩ := Γ.exists_spanningForest O
  exact Module.Finite.of_basis (hF.cycleBasis R)

/-- The integral cycle lattice is free. The instance is stated on the named lattice so
that typeclass search does not have to unfold its definition as a kernel. -/
instance instFreeCycleLattice : Module.Free ℤ (Γ.cycleLattice O) := by
  rw [cycleLattice_def]
  infer_instance

/-- The multigraph cycle-rank formula, including disconnected and empty graphs.
Over `ℤ` this is the integral rank, and over `ZMod 2` it is the binary dimension. -/
theorem finrank_ker_incidenceBoundary_add_card [StrongRankCondition R]
    [Finite Γ.V] [Finite O] :
    Module.finrank R (Γ.incidenceBoundary O R).ker + Nat.card Γ.V =
      Nat.card O + Nat.card (Γ.supportGraph O).ConnectedComponent := by
  obtain ⟨F, hF⟩ := Γ.exists_spanningForest O
  rw [Module.finrank_eq_nat_card_basis (hF.cycleBasis R)]
  have hforest := hF.card_add_card_connectedComponent
  have hsplit := Set.ncard_sdiff_add_ncard_of_subset hF.subset (Set.toFinite O)
  simp only [← Nat.card_coe_set_eq] at hsplit
  omega

end TauCeti.SerreGraph
