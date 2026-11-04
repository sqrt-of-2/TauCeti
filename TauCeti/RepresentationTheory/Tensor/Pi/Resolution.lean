/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.PiTensorProduct
public import TauCeti.RepresentationTheory.Tensor.Pi.Differential
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded.Contraction

/-!
# Contracted tensor products of graded discrete representations

For a finite ordered family of nonnegatively graded discrete representations, a linear
contraction of each factor onto its coefficients gives a contraction of the total tensor
complex onto the tensor product of those coefficients. Only the augmentations need be
equivariant; the projections and homotopies generally are not. Smoothness supplies the joint
continuity of their conjugates required by `TopRep.ResolutionContraction`.

The complex uses the unsigned slot differential, so the factors must have characteristic two.
The homotopy depends on an ordering, but the augmentation is the factorwise tensor product
and does not. This permits invariant tensor products of cocycles from different contracted
resolutions to be interpreted in canonical continuous cohomology.

The construction reuses `TauCeti.LinearContraction.piTensorProduct` for the tensor trick and
`TopRep.ResolutionContraction.ofGraded` for passage from a total module to a cochain complex.

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
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type x} [Fintype ι] [LinearOrder ι]
  (X M : ι → DiscreteRep.{u, v, max v w} R G)
  (ℳ : ∀ i, ℤ → Submodule R (M i).V)
  (hρ : ∀ i n g m, m ∈ ℳ i n → (M i).ρ g m ∈ ℳ i n)
  (d : ∀ i, M i ⟶ M i)
  (hd : ∀ i, LinearMap.IsHomogeneous (d i).toLinearMap (ℳ i) (ℳ i) 1)
  (hdd : ∀ i, (d i).toLinearMap ∘ₗ (d i).toLinearMap = 0)
  (hM : ∀ i (m : (M i).V), m + m = 0)

/-- The total tensor complex of a finite family of graded discrete representations in
characteristic two. Its terms are the total-degree submodules and its differential is the
unsigned slot sum. -/
-- Expose the body so a homogeneous tensor can be supplied as an element of a complex term,
-- just as for `TopRep.gradedCochainComplex` itself.
@[expose] noncomputable def piTensorProductCochainComplex :
    CochainComplex (TopRep.{max u v w x} R G) ℕ := by
  let B := (toSmoothDiscrete R G).obj (piTensorProduct M)
  let D : B.obj ⟶ B.obj := ((toSmoothDiscrete R G).map (piTensorProductDifferential M d)).hom
  have hD : D.hom.toLinearMap = (piTensorProductDifferential M d).toLinearMap :=
    LinearMap.ext (toSmoothDiscrete_map_hom_hom_apply R G _)
  have hDB : LinearMap.IsHomogeneous D.hom.toLinearMap
      (PiTensorProduct.totalDegreePiece ι ℳ) (PiTensorProduct.totalDegreePiece ι ℳ) 1 := by
    rw [hD]
    exact isHomogeneous_piTensorProductDifferential M d ℳ hd
  have hDD : D ≫ D = 0 := by
    ext z
    exact (LinearMap.congr_fun hD _).trans <|
      (congrArg (piTensorProductDifferential M d).toLinearMap
        (LinearMap.congr_fun hD z)).trans
          (LinearMap.congr_fun (piTensorProductDifferential_sq M d hM hdd) z)
  exact B.obj.gradedCochainComplex (PiTensorProduct.totalDegreePiece ι ℳ)
    (piTensorProduct_ρ_mem_totalDegreePiece M ℳ hρ) D hDB hDD

omit [LinearOrder ι] [IsTopologicalGroup G] in
/-- On a homogeneous tensor the complex differential is the unsigned slot sum. -/
@[simp] theorem piTensorProductCochainComplex_d_apply [DecidableEq ι] (n : ℕ)
    (z : PiTensorProduct.totalDegreePiece ι ℳ n) :
    (((piTensorProductCochainComplex M ℳ hρ d hd hdd hM).d n (n + 1)).hom z).1 =
      PiTensorProduct.slotSum ι (fun i ↦ (d i).toLinearMap) z.1 := by
  dsimp only [piTensorProductCochainComplex]
  exact (TopRep.gradedCochainComplex_d_apply ..).trans
    ((toSmoothDiscrete_map_hom_hom_apply R G
      (piTensorProductDifferential M d) z.1).trans
        (LinearMap.congr_fun (piTensorProductDifferential_toLinearMap M d) z.1))

variable
  (c : ∀ i, LinearContraction (d i).toLinearMap (0 : Module.End R (X i).V))
  (hcρ : ∀ i g m, (c i).incl ((X i).ρ g m) = (M i).ρ g ((c i).incl m))
  (hι : ∀ i m, (c i).incl m ∈ ℳ i 0)
  (hneg : ∀ i n, n < 0 → ℳ i n = ⊥)
  (hπ : ∀ i n, n ≠ 0 → ∀ m ∈ ℳ i n, (c i).proj m = 0)
  (hh : ∀ i, LinearMap.IsHomogeneous (c i).homotopy (ℳ i) (ℳ i) (-1))
  (hh₀ : ∀ i m, m ∈ ℳ i 0 → (c i).homotopy m = 0)

/-- Contract the total tensor complex of a finite family of graded discrete representations
onto the tensor product of its coefficients. The input contractions are linear contractions
onto zero differentials, with equivariant augmentations in degree zero, projections supported
in degree zero, and homotopies vanishing there. The output is a contraction in topological
representations, with unsigned tensor differential and total-degree grading. -/
noncomputable def piTensorProductResolutionContraction :
    TopRep.ResolutionContraction.{u, v, max u w x}
      ((toSmoothDiscrete R G).obj (piTensorProduct X)).obj
      (piTensorProductCochainComplex M ℳ hρ d hd hdd hM) :=
  let B := (toSmoothDiscrete R G).obj (piTensorProduct M)
  let A := (toSmoothDiscrete R G).obj (piTensorProduct X)
  let D : B.obj ⟶ B.obj := ((toSmoothDiscrete R G).map (piTensorProductDifferential M d)).hom
  have hD : D.hom.toLinearMap = (piTensorProductDifferential M d).toLinearMap :=
    LinearMap.ext (toSmoothDiscrete_map_hom_hom_apply R G _)
  have hDB : LinearMap.IsHomogeneous D.hom.toLinearMap
      (PiTensorProduct.totalDegreePiece ι ℳ) (PiTensorProduct.totalDegreePiece ι ℳ) 1 := by
    rw [hD]
    exact isHomogeneous_piTensorProductDifferential M d ℳ hd
  have hDD : D ≫ D = 0 := by
    ext z
    exact (LinearMap.congr_fun hD _).trans <|
      (congrArg (piTensorProductDifferential M d).toLinearMap
        (LinearMap.congr_fun hD z)).trans
          (LinearMap.congr_fun (piTensorProductDifferential_sq M d hM hdd) z)
  -- Tensor the equivariant inclusions to obtain the augmentation into total degree zero.
  let I : ∀ i, X i ⟶ M i := fun i ↦
    { toLinearMap := (c i).incl
      isIntertwining' g := LinearMap.ext (hcρ i g) }
  let J : A.obj ⟶ B.obj :=
    ((toSmoothDiscrete R G).map (Representation.IntertwiningMap.piTensorProduct I)).hom
  have hJ (z : (piTensorProduct X).V) :
      J.hom z = PiTensorProduct.map (fun i ↦ (c i).incl) z :=
    (toSmoothDiscrete_map_hom_hom_apply R G _ z).trans
      (LinearMap.congr_fun (Representation.IntertwiningMap.piTensorProduct_toLinearMap I) z)
  have hJ₀ (z : (piTensorProduct X).V) :
      J.hom z ∈ PiTensorProduct.totalDegreePiece ι ℳ 0 :=
    (congrArg (· ∈ PiTensorProduct.totalDegreePiece ι ℳ 0) (hJ z)).mpr
      (PiTensorProduct.map_mem_totalDegreePiece_zero hι z)
  -- The ordered algebraic tensor contraction respects the total grading.
  let C := LinearContraction.piTensorProduct c hM
  have hH : LinearMap.IsHomogeneous C.homotopy
      (PiTensorProduct.totalDegreePiece ι ℳ) (PiTensorProduct.totalDegreePiece ι ℳ) (-1) := by
    rw [LinearContraction.piTensorProduct_homotopy]
    refine PiTensorProduct.isHomogeneous_slotHomotopy (fun i ↦ ?_) hh
    rw [LinearMap.isHomogeneous_def]
    intro p m hm
    rw [add_zero, LinearMap.comp_apply]
    by_cases hp : p = 0
    · subst p
      exact hι i _
    · rw [hπ i p hp m hm, map_zero]
      exact zero_mem _
  TopRep.ResolutionContraction.ofGraded.{u, v, max u w x} A.obj J hJ₀ C.proj C.homotopy hH
    (fun z ↦ by
      refine (congrArg C.proj (hJ z)).trans ?_
      simpa only [C, LinearContraction.piTensorProduct_incl] using C.proj_incl_apply z)
    (fun n z hz ↦ by
      rw [LinearContraction.piTensorProduct_proj]
      exact PiTensorProduct.map_eq_zero_of_mem_totalDegreePiece_of_pos
        (fun i p hp m hm ↦ hπ i p hp.ne' m hm) (Int.natCast_pos.2 n.succ_pos) hz)
    (fun z hz ↦ by
      rw [LinearContraction.piTensorProduct_homotopy]
      exact PiTensorProduct.slotHomotopy_eq_zero_of_mem_totalDegreePiece_zero hneg hh₀ hz)
    (fun (z : ⨂[R] i, (M i).V) ↦ by
      -- Transfer the algebraic contraction identity using the characteristic equations
      -- of the bundled differential and augmentation, on their common tensor carrier.
      have hD' (y : ⨂[R] i, (M i).V) :
          D.hom y = PiTensorProduct.slotSum ι (fun i ↦ (d i).toLinearMap) y :=
        (LinearMap.congr_fun hD y).trans
          (LinearMap.congr_fun (piTensorProductDifferential_toLinearMap M d) y)
      have e : PiTensorProduct.slotSum ι (fun i ↦ (d i).toLinearMap) (C.homotopy z) +
          C.homotopy (PiTensorProduct.slotSum ι (fun i ↦ (d i).toLinearMap) z) =
            z - C.incl (C.proj z) :=
        LinearMap.congr_fun C.dM_comp_homotopy_add_homotopy_comp_dM z
      exact (congrArg₂ (fun a b : ⨂[R] i, (M i).V ↦ a + b)
        (hD' (C.homotopy z)) (congrArg C.homotopy (hD' z))).trans <|
          e.trans (congrArg (z - ·) <|
            (LinearMap.congr_fun (LinearContraction.piTensorProduct_incl c hM) _).trans
              (hJ (C.proj z)).symm))
    (IsSmoothDiscrete.continuous_conj B.property A.property C.proj)
    (IsSmoothDiscrete.continuous_conj B.property B.property C.homotopy)
    (hρ := piTensorProduct_ρ_mem_totalDegreePiece M ℳ hρ) (hd := hDB) (hdd := hDD)

/-- The tensor resolution contraction augments coefficients factor by factor. -/
@[simp] theorem piTensorProductResolutionContraction_ι_apply (z : (piTensorProduct X).V) :
    ((piTensorProductResolutionContraction X M ℳ hρ d hd hdd hM c hcρ hι hneg hπ hh hh₀).ι.hom
      z).1 = PiTensorProduct.map (fun i ↦ (c i).incl) z := by
  let I : ∀ i, X i ⟶ M i := fun i ↦
    { toLinearMap := (c i).incl
      isIntertwining' g := LinearMap.ext (hcρ i g) }
  dsimp only [piTensorProductResolutionContraction]
  refine (congrArg (fun f : ((toSmoothDiscrete R G).obj (piTensorProduct X)).obj ⟶
      (piTensorProductCochainComplex M ℳ hρ d hd hdd hM).X 0 ↦ (f.hom z).1)
    (TopRep.ResolutionContraction.ofGraded_ι ..)).trans ?_
  exact (TopRep.gradedCochainComplexLift_apply ..).trans
    ((toSmoothDiscrete_map_hom_hom_apply R G
      (X := piTensorProduct X) (Y := piTensorProduct M)
      (Representation.IntertwiningMap.piTensorProduct I) z).trans
        (LinearMap.congr_fun (Representation.IntertwiningMap.piTensorProduct_toLinearMap I) z))

/-- The tensor resolution contraction projects coefficients factor by factor. -/
@[simp] theorem piTensorProductResolutionContraction_proj_apply
    (z : PiTensorProduct.totalDegreePiece ι ℳ 0) :
    (piTensorProductResolutionContraction X M ℳ hρ d hd hdd hM c hcρ hι hneg hπ hh hh₀).proj z =
      PiTensorProduct.map (fun i ↦ (c i).proj) z.1 := by
  dsimp only [piTensorProductResolutionContraction]
  exact (TopRep.ResolutionContraction.ofGraded_proj_apply ..).trans
    (LinearMap.congr_fun (LinearContraction.piTensorProduct_proj c hM) z.1)

/-- The tensor resolution contraction uses the ordered slot homotopy in positive degrees. -/
@[simp] theorem piTensorProductResolutionContraction_hom_apply (n : ℕ)
    (z : PiTensorProduct.totalDegreePiece ι ℳ (n + 1 : ℕ)) :
    ((piTensorProductResolutionContraction X M ℳ hρ d hd hdd hM c hcρ hι hneg hπ hh hh₀).hom n
      z).1 = PiTensorProduct.slotHomotopy ι (fun i ↦ (c i).incl ∘ₗ (c i).proj)
        (fun i ↦ (c i).homotopy) z.1 := by
  dsimp only [piTensorProductResolutionContraction]
  exact (TopRep.ResolutionContraction.ofGraded_hom_apply ..).trans
    (LinearMap.congr_fun (LinearContraction.piTensorProduct_homotopy c hM) z.1)

end TauCeti.DiscreteRep

section Example

open TauCeti CategoryTheory

-- Use the scalar structure carried by the coefficient dictionary rather than the fallback
-- integer module structure when forming morphisms of discrete representations.
attribute [local instance 1100] DiscreteRep.module

/-- Two canonical coinduced resolutions, with possibly different smooth mod-two coefficients,
can be tensored without requiring their contracting homotopies to be equivariant. -/
example {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (A : Fin 2 → SmoothDiscreteTopRep.{0, u, u} (ZMod 2) G) :
    ∃ K : CochainComplex (TopRep.{u} (ZMod 2) G) ℕ,
      Nonempty (TopRep.ResolutionContraction
        ((toSmoothDiscrete (ZMod 2) G).obj
          (DiscreteRep.piTensorProduct
            (fun i ↦ (ofSmoothDiscrete (ZMod 2) G).obj (A i)))).obj K) := by
  let X := fun i ↦ (ofSmoothDiscrete (ZMod 2) G).obj (A i)
  let M := fun i ↦ (ofSmoothDiscrete (ZMod 2) G).obj (smoothGradedResolutionFunctor.obj (A i))
  let d : ∀ i, M i ⟶ M i := fun i ↦
    (ofSmoothDiscrete (ZMod 2) G).map (smoothGradedResolutionDifferential (A i))
  have hd (i) : (d i).toLinearMap = (A i).obj.gradedResolutionDifferential :=
    (ofSmoothDiscrete_map_toLinearMap _ _ _).trans
      (LinearMap.ext (smoothGradedResolutionDifferential_hom_apply (A i)))
  -- Evaluation at one is the projection and homotopy; constants give the inclusion.
  let c (i : Fin 2) : LinearContraction (d i).toLinearMap (0 : Module.End (ZMod 2) (X i).V) := {
    incl := (A i).obj.gradedResolutionAugmentation
    proj := (A i).obj.gradedResolutionProjection
    homotopy := (A i).obj.gradedResolutionHomotopy
    dM_comp_incl := by
      rw [hd]
      exact LinearMap.ext fun x ↦ ((A i).obj.gradedResolutionDifferential_augmentation x).trans
        (map_zero (A i).obj.gradedResolutionAugmentation).symm
    proj_comp_dM := by
      rw [hd]
      exact LinearMap.ext (A i).obj.gradedResolutionProjection_differential
    proj_comp_incl := LinearMap.ext (A i).obj.gradedResolutionProjection_augmentation
    dM_comp_homotopy_add_homotopy_comp_dM := by
      rw [hd]
      exact LinearMap.ext (A i).obj.gradedResolutionDifferential_gradedResolutionHomotopy_add }
  let ℳ := fun i ↦ (A i).obj.gradedResolutionPiece
  have hρ : ∀ i n g m, m ∈ ℳ i n → (M i).ρ g m ∈ ℳ i n := by
    intro i n g m hm
    exact (A i).obj.gradedResolutionTopRep_ρ_mem n g m hm
  have hdegree : ∀ i, LinearMap.IsHomogeneous (d i).toLinearMap (ℳ i) (ℳ i) 1 := by
    intro i
    rw [hd]
    exact (A i).obj.isHomogeneous_gradedResolutionDifferential
  have hsquare : ∀ i, (d i).toLinearMap ∘ₗ (d i).toLinearMap = 0 := by
    intro i
    rw [hd]
    exact LinearMap.ext (A i).obj.gradedResolutionDifferential_sq
  have hM : ∀ i (m : (M i).V), m + m = 0 := fun i ↦
    (A i).obj.gradedResolutionModule_add_self_eq_zero fun a ↦ by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  -- The tensor complex retains both differentials; only their squares and cross terms vanish.
  refine ⟨DiscreteRep.piTensorProductCochainComplex M ℳ hρ d hdegree hsquare hM, ⟨?_⟩⟩
  exact DiscreteRep.piTensorProductResolutionContraction X M ℳ hρ d hdegree hsquare hM c
    (fun i g x ↦ (A i).obj.gradedResolutionAugmentation_equivariant g x)
    (fun i ↦ (A i).obj.gradedResolutionAugmentation_mem)
    (fun i n hn ↦ (A i).obj.gradedResolutionPiece_of_neg hn)
    (fun i n hn m hm ↦ (A i).obj.gradedResolutionProjection_eq_zero_of_mem hn hm)
    (fun i ↦ (A i).obj.isHomogeneous_gradedResolutionHomotopy)
    (fun i m hm ↦ (A i).obj.gradedResolutionHomotopy_eq_zero_of_mem_zero hm)

end Example
