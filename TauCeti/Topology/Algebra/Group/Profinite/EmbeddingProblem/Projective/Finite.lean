/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Projective.Basic

/-!
# Finite embedding problems of projective pro-`p` groups

For a pro-`p` topological group, projectivity is equivalent to solvability of all finite
embedding problems with `p`-group kernel. In such a problem the finite quotient is a `p`-group,
so the covering group is also a `p`-group. Projectivity therefore gives a continuous lift.
Combined with the inverse-limit lifting theorem, this characterizes projectivity by finite
embedding problems without a finite-generation hypothesis.

The source needs only a topological group structure. Compactness and total disconnectedness
are required of the covering groups in the definition of projectivity, not of the source.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.6.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A projective pro-`p` topological group solves every finite embedding problem with
`p`-group kernel. Neither compactness nor finite generation of the source is needed. -/
theorem hasPGroupSolutions_of_isProjective (hG : IsProP p G)
    (hproj : IsProjective.{u, u, u} p G) : HasPGroupSolutions p G := by
  refine hasPGroupSolutions_iff.mpr fun P hP ↦ ?_
  let _ : TopologicalSpace P.Q := ⊥
  let _ : TopologicalSpace P.E := ⊥
  have : DiscreteTopology P.Q := ⟨rfl⟩
  have : DiscreteTopology P.E := ⟨rfl⟩
  have hπ : Continuous P.π := P.π.continuous_iff_isOpen_ker.mpr P.isOpen_ker_π
  have hQ : IsPGroup p P.Q :=
    isProP_iff_isPGroup.mp (hG.of_surjective P.π hπ P.π_surjective)
  have hE : IsPGroup p P.E := IsPGroup.of_subgroup_of_quotient hP
    (hQ.of_equiv (QuotientGroup.quotientKerEquivOfSurjective P.α P.α_surjective).symm)
  obtain ⟨φ, hφ⟩ := hproj.exists_continuous_lift hE.isProP
    ⟨P.α, continuous_of_discreteTopology⟩ P.α_surjective ⟨P.π, hπ⟩
  exact ⟨φ.toMonoidHom, FiniteEmbeddingProblem.isSolution_iff.mpr
    ⟨φ.toMonoidHom.continuous_iff_isOpen_ker.mp φ.continuous,
      MonoidHom.ext fun g ↦ DFunLike.congr_fun hφ g⟩⟩

/-- A pro-`p` topological group is projective exactly when every finite embedding problem
with `p`-group kernel has a solution. -/
theorem isProjective_iff_hasPGroupSolutions (hG : IsProP p G) :
    IsProjective.{u, u, u} p G ↔ HasPGroupSolutions p G :=
  ⟨hasPGroupSolutions_of_isProjective hG, isProjective_of_hasPGroupSolutions⟩

end TauCeti
