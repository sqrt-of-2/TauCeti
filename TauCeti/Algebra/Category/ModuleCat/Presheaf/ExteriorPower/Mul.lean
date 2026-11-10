/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.ExteriorPower.Mul
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Multiplication of exterior powers of presheaves of modules

The sectionwise wedge product gives `⋀ⁱ M ⊗ ⋀ʲ M ⟶ ⋀ⁱ⁺ʲ M`, naturally in the presheaf `M`.
It is associative, unital in degree zero, and graded commutative with sign `(-1)^(i*j)`.
Sheafifying these maps supplies exterior multiplication for sheaves of modules.

This follows the construction of `PresheafOfModulesOfCommRing.symmetricPowerMul`, with
Mathlib's exterior wedge in place of symmetric multiplication (Stacks Project, Tags 01CF, 01CG).
-/

public section

open CategoryTheory MonoidalCategory

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Exterior multiplication of presheaves of modules, computed by the wedge product on sections. -/
def exteriorPowerMul (M : PresheafOfModulesOfCommRing.{u} R) (i j : ℕ) :
    (exteriorPower i).obj M ⊗ (exteriorPower j).obj M ⟶ (exteriorPower (i + j)).obj M :=
  homMk (fun X ↦ ModuleCat.exteriorPower.mul (M.obj X) i j) (fun {X Y} f ↦ by
    refine ModuleCat.exteriorPower.tensor_hom_ext fun x y ↦ ?_
    -- Restriction-of-scalars and sectionwise tensor objects are bundled wrappers, so `erw`
    -- is needed to apply the elementwise restriction formula.
    erw [ModuleCat.comp_apply, Monoidal.tensorObj_map_tmul, ModuleCat.restrictScalars.map_apply,
      ModuleCat.comp_apply, exteriorPower_obj_map_mk, exteriorPower_obj_map_mk,
      ModuleCat.exteriorPower.mul_tmul, _root_.exteriorPower.wedge_ιMulti,
      ModuleCat.exteriorPower.mul_tmul, _root_.exteriorPower.wedge_ιMulti,
      exteriorPower_obj_map_mk]
    congr 1
    funext k
    exact Fin.addCases
      (fun a ↦ (Fin.append_left _ _ a).trans (congrArg (M.map f) (Fin.append_left x y a)).symm)
      (fun b ↦ (Fin.append_right _ _ b).trans (congrArg (M.map f) (Fin.append_right x y b)).symm) k)

/-- Exterior multiplication is computed sectionwise. -/
@[simp]
lemma exteriorPowerMul_app (M : PresheafOfModulesOfCommRing.{u} R) (i j : ℕ) (X : Cᵒᵖ) :
    (exteriorPowerMul M i j).app X = ModuleCat.exteriorPower.mul (M.obj X) i j :=
  (rfl)

private lemma eqToHom_exteriorPower_app (M : PresheafOfModulesOfCommRing.{u} R) {i j : ℕ}
    (h : i = j) (X : Cᵒᵖ) :
    (eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) h)).app X =
      eqToHom (congrArg (M.obj X).exteriorPower h) := by
  subst h
  rfl

/-- Exterior multiplication is natural in the presheaf of modules. -/
@[reassoc]
lemma exteriorPowerMul_naturality {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (i j : ℕ) :
    ((exteriorPower i).map φ ⊗ₘ (exteriorPower j).map φ) ≫ exteriorPowerMul N i j =
      exteriorPowerMul M i j ≫ (exteriorPower (i + j)).map φ := by
  ext1 X
  simp only [PresheafOfModules.comp_app, tensorHom_app, exteriorPower_map_app,
    exteriorPowerMul_app]
  exact ModuleCat.exteriorPower.mul_naturality (φ.app' X) i j

/-- Exterior multiplication is associative, up to the canonical identification of degrees. -/
@[reassoc]
lemma exteriorPowerMul_assoc (M : PresheafOfModulesOfCommRing.{u} R) (i j k : ℕ) :
    (exteriorPowerMul M i j ▷ (exteriorPower k).obj M) ≫ exteriorPowerMul M (i + j) k =
      (α_ _ _ _).hom ≫ ((exteriorPower i).obj M ◁ exteriorPowerMul M j k) ≫
        exteriorPowerMul M i (j + k) ≫
          eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (add_assoc i j k).symm) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    exteriorPowerMul_app]
  rw [eqToHom_exteriorPower_app M (add_assoc i j k).symm]
  exact ModuleCat.exteriorPower.mul_assoc (M.obj X) i j k

/-- Exterior multiplication is graded commutative with the Koszul sign. -/
@[reassoc]
lemma exteriorPowerMul_comm (M : PresheafOfModulesOfCommRing.{u} R) (i j : ℕ) :
    (β_ ((exteriorPower i).obj M) ((exteriorPower j).obj M)).hom ≫ exteriorPowerMul M j i =
      (-1 : ℤ) ^ (i * j) • (exteriorPowerMul M i j ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (add_comm i j))) := by
  ext1 X
  simp only [PresheafOfModules.zsmul_app, PresheafOfModules.comp_app,
    braiding_hom_app, exteriorPowerMul_app]
  rw [eqToHom_exteriorPower_app M (add_comm i j)]
  exact ModuleCat.exteriorPower.mul_comm (M.obj X) i j

/-- The degree-zero identification is a left unit for exterior multiplication. -/
@[reassoc]
lemma exteriorPowerMul_one_mul (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    ((exteriorPowerZeroIso R).inv.app M ▷ (exteriorPower n).obj M) ≫
        exteriorPowerMul M 0 n =
      (λ_ ((exteriorPower n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (zero_add n).symm) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, whiskerRight_app, leftUnitor_hom_app,
    exteriorPowerMul_app, exteriorPowerZeroIso_inv_app_app]
  rw [eqToHom_exteriorPower_app M (zero_add n).symm]
  exact ModuleCat.exteriorPower.one_mul (M.obj X) n

/-- The degree-zero identification is a right unit for exterior multiplication. -/
@[reassoc]
lemma exteriorPowerMul_mul_one (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    ((exteriorPower n).obj M ◁ (exteriorPowerZeroIso R).inv.app M) ≫
        exteriorPowerMul M n 0 =
      (ρ_ ((exteriorPower n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (add_zero n).symm) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, whiskerLeft_app, rightUnitor_hom_app,
    exteriorPowerMul_app, exteriorPowerZeroIso_inv_app_app]
  rw [eqToHom_exteriorPower_app M (add_zero n).symm]
  exact ModuleCat.exteriorPower.mul_one (M.obj X) n

end PresheafOfModulesOfCommRing
