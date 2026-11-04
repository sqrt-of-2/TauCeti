/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum

/-!
# Finite tensor products of linear contractions in characteristic two

A finite family of linear contractions onto modules with zero differential gives a contraction
of their tensor product. The differential is the unsigned slot sum. The homotopy uses the
chosen order of the factors, applying inclusion after projection in earlier slots and the
factor's homotopy in the active slot. This packages the dependent-family tensor trick of
`TauCeti.PiTensorProduct.slotSum_comp_slotHomotopy_add` as a `TauCeti.LinearContraction`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–6.
-/

public section

namespace TauCeti.LinearContraction

open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R] {ι : Type x} [Fintype ι] [LinearOrder ι]
  {M : ι → Type v} {N : ι → Type w}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  {d : ∀ i, Module.End R (M i)} (c : ∀ i, LinearContraction (d i) (0 : Module.End R (N i)))
  (hM : ∀ i (m : M i), m + m = 0)

/-- Tensor a finite family of contractions onto modules with zero differential, in
characteristic two. The homotopy depends on the chosen order, but the inclusion and projection
do not. No side conditions on the factor homotopies are required. -/
noncomputable def piTensorProduct :
    LinearContraction (PiTensorProduct.slotSum ι d) (0 : Module.End R (⨂[R] i, N i)) where
  incl := PiTensorProduct.map fun i ↦ (c i).incl
  proj := PiTensorProduct.map fun i ↦ (c i).proj
  homotopy := PiTensorProduct.slotHomotopy ι (fun i ↦ (c i).incl ∘ₗ (c i).proj)
    (fun i ↦ (c i).homotopy)
  dM_comp_incl := by
    simpa only [PiTensorProduct.slotSum_zero, LinearMap.comp_zero] using
      PiTensorProduct.slotSum_comp_map (f' := (0 : ∀ i, Module.End R (N i)))
        (fun i ↦ (c i).incl) (fun i ↦ (c i).dM_comp_incl)
  proj_comp_dM := by
    simpa only [PiTensorProduct.slotSum_zero, LinearMap.zero_comp] using
      (PiTensorProduct.slotSum_comp_map (f := (0 : ∀ i, Module.End R (N i)))
        (fun i ↦ (c i).proj) (fun i ↦ (c i).proj_comp_dM.symm)).symm
  proj_comp_incl := by
    rw [← PiTensorProduct.map_comp]
    simp
  dM_comp_homotopy_add_homotopy_comp_dM := by
    rw [← PiTensorProduct.map_comp]
    exact PiTensorProduct.slotSum_comp_slotHomotopy_add hM
      (fun i ↦ by simp [LinearMap.comp_assoc])
      (fun i ↦ (c i).dM_comp_homotopy_add_homotopy_comp_dM)

/-- The inclusion of the tensor contraction is the tensor product of the inclusions. -/
@[simp] theorem piTensorProduct_incl :
    (piTensorProduct c hM).incl = PiTensorProduct.map fun i ↦ (c i).incl := (rfl)

/-- The projection of the tensor contraction is the tensor product of the projections. -/
@[simp] theorem piTensorProduct_proj :
    (piTensorProduct c hM).proj = PiTensorProduct.map fun i ↦ (c i).proj := (rfl)

/-- The homotopy of the tensor contraction is the ordered slot homotopy. -/
@[simp] theorem piTensorProduct_homotopy :
    (piTensorProduct c hM).homotopy =
      PiTensorProduct.slotHomotopy ι (fun i ↦ (c i).incl ∘ₗ (c i).proj)
        (fun i ↦ (c i).homotopy) := (rfl)

end TauCeti.LinearContraction
