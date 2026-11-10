/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Mul
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
public import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# Multiplication of exterior powers of sheaves of modules

For a sheaf of modules `M` over a sheaf of commutative rings, construct the natural wedge product
`⋀ⁱ M ⊗ ⋀ʲ M ⟶ ⋀ⁱ⁺ʲ M`. It is associative, unital through the degree-zero identification with
the structure sheaf, and graded commutative with Koszul sign `(-1)^(i*j)`.

These are the products used to multiply local exterior products in constructing determinants
of extensions of vector bundles. No local freeness or quasi-coherence is required.

The construction follows `SheafOfModules.symmetricPowerMul`: sheafify the sectionwise wedge
product and precompose with the monoidal tensor comparison of sheafification. The mathematical
references are the Stacks Project, Tags 01CF and 01CG.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

namespace SheafOfModules

/-- Exterior multiplication of sheaves of modules: the sheafified sectionwise wedge product,
preceded by the tensor comparison of sheafification. -/
def exteriorPowerMul (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (exteriorPower R i).obj M ⊗ (exteriorPower R j).obj M ⟶ (exteriorPower R (i + j)).obj M :=
  ((exteriorPowerIso i M).hom ⊗ₘ (exteriorPowerIso j M).hom) ≫
    Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (PresheafOfModulesOfCommRing.exteriorPowerMul M.val i j) ≫
      (exteriorPowerIso (i + j) M).inv

/-- The defining equation of sheaf exterior multiplication through the identifications with
sheafified sectionwise exterior powers. -/
theorem exteriorPowerMul_def (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    exteriorPowerMul M i j =
      ((exteriorPowerIso i M).hom ⊗ₘ (exteriorPowerIso j M).hom) ≫
        Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
            (PresheafOfModulesOfCommRing.exteriorPowerMul M.val i j) ≫
          (exteriorPowerIso (i + j) M).inv :=
  (rfl)

/-- Exterior multiplication is natural in the sheaf of modules. -/
@[reassoc]
theorem exteriorPowerMul_naturality {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N)
    (i j : ℕ) :
    ((exteriorPower R i).map φ ⊗ₘ (exteriorPower R j).map φ) ≫ exteriorPowerMul N i j =
      exteriorPowerMul M i j ≫ (exteriorPower R (i + j)).map φ :=
  GradedObject.map_mul_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M)
    (Y' := fun n ↦ (exteriorPower R n).obj N) (e' := fun n ↦ exteriorPowerIso n N) _ _
    (exteriorPowerMul_def N) _ _ (fun n ↦ exteriorPower_map n φ)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_naturality φ.val) i j

/-- Exterior multiplication is associative, up to the canonical identification of degrees. -/
@[reassoc]
theorem exteriorPowerMul_assoc (M : SheafOfModules.{u} (ringCatSheaf R)) (i j k : ℕ) :
    (exteriorPowerMul M i j ▷ (exteriorPower R k).obj M) ≫ exteriorPowerMul M (i + j) k =
      (α_ _ _ _).hom ≫ ((exteriorPower R i).obj M ◁ exteriorPowerMul M j k) ≫
        exteriorPowerMul M i (j + k) ≫
          eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (add_assoc i j k).symm) :=
  GradedObject.mul_assoc_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_assoc M.val) i j k

private theorem exteriorPowerZeroIso_inv_app_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPowerZeroIso R).inv.app M =
      Functor.LaxMonoidal.ε (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).inv.app M.val) ≫
        (exteriorPowerIso 0 M).inv := by
  have h : (exteriorPowerZeroIso R).inv.app M =
      (exteriorPowerIso 0 M ≪≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
          ((PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).app M.val) ≪≫
        TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
          (SheafOfModules.unit (ringCatSheaf R))).inv :=
    (by
      rw [← Iso.app_inv]
      exact (Iso.inv_eq_inv ((exteriorPowerZeroIso R).app M) _).2
        (exteriorPowerZeroIso_hom_app M))
  rw [h]
  -- The inner composite uses presheaves over `R.obj`, the outer one `ringCatSheaf R`.
  erw [Iso.trans_inv, Iso.trans_inv, Functor.mapIso_inv]
  rw [TauCeti.SheafOfModules.sheafification_ε, Category.assoc]
  congr 1
  -- Both identifications are the counit at the unit sheaf, with different unit wrappers.
  exact (Iso.inv_eq_inv _ _).2 ((TauCeti.SheafOfModules.sheafificationIso_hom _ _).trans
    (TauCeti.SheafOfModules.sheafificationUnitIso_hom R).symm)

/-- The degree-zero identification is a left unit for exterior multiplication. -/
@[reassoc]
theorem exteriorPowerMul_one_mul (M : SheafOfModules.{u} (ringCatSheaf R)) (n : ℕ) :
    ((exteriorPowerZeroIso R).inv.app M ▷ (exteriorPower R n).obj M) ≫
        exteriorPowerMul M 0 n =
      (λ_ ((exteriorPower R n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (zero_add n).symm) :=
  GradedObject.one_mul_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M) _ _
    (exteriorPowerZeroIso_inv_app_eq M)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_one_mul M.val) n

/-- The degree-zero identification is a right unit for exterior multiplication. -/
@[reassoc]
theorem exteriorPowerMul_mul_one (M : SheafOfModules.{u} (ringCatSheaf R)) (n : ℕ) :
    ((exteriorPower R n).obj M ◁ (exteriorPowerZeroIso R).inv.app M) ≫
        exteriorPowerMul M n 0 =
      (ρ_ ((exteriorPower R n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (add_zero n).symm) :=
  GradedObject.mul_one_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M) _ _
    (exteriorPowerZeroIso_inv_app_eq M)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_mul_one M.val) n

/-- Exterior multiplication is graded commutative with Koszul sign `(-1)^(i*j)`. -/
@[reassoc]
theorem exteriorPowerMul_comm (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (β_ ((exteriorPower R i).obj M) ((exteriorPower R j).obj M)).hom ≫
        exteriorPowerMul M j i =
      (-1 : ℤ) ^ (i * j) • (exteriorPowerMul M i j ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (add_comm i j))) := by
  let F := PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)
  have : F.Additive := F.additive_of_preserves_binary_products
  exact GradedObject.mul_comm_zsmul_of_laxBraided
    (Y := fun n ↦ (exteriorPower R n).obj M) (e := fun n ↦ exteriorPowerIso n M)
    _ _ (exteriorPowerMul_def M) (fun i j ↦ (-1 : ℤ) ^ (i * j))
    (PresheafOfModulesOfCommRing.exteriorPowerMul_comm M.val) i j

end SheafOfModules
