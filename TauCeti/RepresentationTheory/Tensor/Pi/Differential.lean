/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Pi.Discrete
public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum

/-!
# Differentials on finite tensor products of discrete representations

The unsigned tensor differential applies the differential in one factor at a time. It is
equivariant for the diagonal group action and raises total degree by one. In characteristic
two it squares to zero. The factors may be different representations, as is necessary for
products of resolutions indexed by double cosets.

This bundles the linear slot sum of `TauCeti.PiTensorProduct.slotSum`; no choice of ordering
of the factors is needed for the differential.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–6.
-/

public section

namespace TauCeti.DiscreteRep

open CategoryTheory
open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Monoid G] [TopologicalSpace G]
  {ι : Type x} [Fintype ι] (M : ι → DiscreteRep.{u, v, w} R G)
  (d : ∀ i, M i ⟶ M i)

/-- The unsigned differential on a finite tensor product: apply `d i` in each slot and sum.
It is a differential when the factors have square-zero differentials and characteristic two. -/
noncomputable def piTensorProductDifferential : piTensorProduct M ⟶ piTensorProduct M := by
  classical
  refine { toLinearMap := PiTensorProduct.slotSum ι (fun i ↦ (d i).toLinearMap)
           isIntertwining' := fun g ↦ ?_ }
  -- The carrier of the bundled tensor product is the algebraic tensor product, but its
  -- representation is opaque; expose its action before using the linear slot-sum identity.
  have hρ : (piTensorProduct M).ρ g = PiTensorProduct.map (fun i ↦ (M i).ρ g) :=
    LinearMap.ext fun z ↦ (piTensorProduct_ρ_apply M g z).trans
      (LinearMap.congr_fun (Representation.piTensorProduct_apply _ g) z)
  rw [hρ]
  exact PiTensorProduct.slotSum_comp_map (fun i ↦ (M i).ρ g)
    (fun i ↦ (d i).isIntertwining' g)

/-- The bundled tensor differential acts by the linear slot sum. -/
theorem piTensorProductDifferential_toLinearMap [DecidableEq ι] :
    (piTensorProductDifferential M d).toLinearMap =
      PiTensorProduct.slotSum ι (fun i ↦ (d i).toLinearMap) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  rfl

/-- On pure tensors, the differential is the sum of tensors with one differentiated factor. -/
@[simp] theorem piTensorProductDifferential_tprod [DecidableEq ι] (m : ∀ i, (M i).V) :
    (piTensorProductDifferential M d).toLinearMap (PiTensorProduct.tprod R m) =
      ∑ i, PiTensorProduct.tprod R (Function.update m i ((d i).toLinearMap (m i))) :=
  (LinearMap.congr_fun (piTensorProductDifferential_toLinearMap M d) _).trans
    (PiTensorProduct.slotSum_tprod _ m)

/-- If each factor differential raises degree by one, so does the tensor differential. -/
theorem isHomogeneous_piTensorProductDifferential
    (ℳ : ∀ i, ℤ → Submodule R (M i).V)
    (hd : ∀ i, LinearMap.IsHomogeneous (d i).toLinearMap (ℳ i) (ℳ i) 1) :
    LinearMap.IsHomogeneous (piTensorProductDifferential M d).toLinearMap
      (PiTensorProduct.totalDegreePiece ι ℳ) (PiTensorProduct.totalDegreePiece ι ℳ) 1 := by
  classical
  rw [piTensorProductDifferential_toLinearMap]
  exact PiTensorProduct.isHomogeneous_slotSum hd

/-- The unsigned tensor differential squares to zero in characteristic two. -/
@[simp] theorem piTensorProductDifferential_sq
    (hM : ∀ i (m : (M i).V), m + m = 0)
    (hdd : ∀ i, (d i).toLinearMap ∘ₗ (d i).toLinearMap = 0) :
    (piTensorProductDifferential M d).toLinearMap ∘ₗ
      (piTensorProductDifferential M d).toLinearMap = 0 := by
  classical
  rw [piTensorProductDifferential_toLinearMap]
  exact PiTensorProduct.slotSum_comp_slotSum hM hdd

/-- The diagonal group action preserves total degree if it preserves the degree in each factor. -/
theorem piTensorProduct_ρ_mem_totalDegreePiece
    (ℳ : ∀ i, ℤ → Submodule R (M i).V)
    (hρ : ∀ i n g m, m ∈ ℳ i n → (M i).ρ g m ∈ ℳ i n)
    (n : ℤ) (g : G) (z : (piTensorProduct M).V)
    (hz : z ∈ PiTensorProduct.totalDegreePiece ι ℳ n) :
    (piTensorProduct M).ρ g z ∈ PiTensorProduct.totalDegreePiece ι ℳ n := by
  have h := PiTensorProduct.isHomogeneous_map (ℳ := ℳ) (𝒩 := ℳ)
    (a := fun _ ↦ (0 : ℤ)) (g := fun i ↦ (M i).ρ g)
    (fun i ↦ LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
      simpa using hρ i p g m hm)
  rw [Finset.sum_const_zero] at h
  have hz' := h.map_mem hz
  rw [add_zero] at hz'
  exact (congrArg (· ∈ PiTensorProduct.totalDegreePiece ι ℳ n)
    ((piTensorProduct_ρ_apply M g z).trans
      (LinearMap.congr_fun (Representation.piTensorProduct_apply _ g) z))).mpr hz'

end TauCeti.DiscreteRep
