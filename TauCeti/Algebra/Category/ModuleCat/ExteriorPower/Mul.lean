/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Multiplication of exterior powers in the category of modules

Package Mathlib's `exteriorPower.wedge` as a tensor-product morphism, with its naturality,
associativity and unit laws. On decomposable elements multiplication concatenates the vector
families, in that order. These maps provide sectionwise exterior multiplication for presheaves
and sheaves of modules (Stacks Project, Tags 01CF and 01CG).

The construction parallels `ModuleCat.symmetricPower.mul`, using the exterior-algebra product
rather than the symmetric-algebra product.
-/

public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- Maps from a tensor product of exterior powers are determined on tensors of decomposable
exterior products. -/
lemma tensor_hom_ext {M N P : ModuleCat.{u} R} {i j : ℕ}
    {f g : M.exteriorPower i ⊗ N.exteriorPower j ⟶ P}
    (h : ∀ (x : Fin i → M) (y : Fin j → N), f (mk x ⊗ₜ mk y) = g (mk x ⊗ₜ mk y)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply _root_.exteriorPower.linearMap_ext
  apply _root_.AlternatingMap.ext
  intro x
  apply _root_.exteriorPower.linearMap_ext
  apply _root_.AlternatingMap.ext
  intro y
  exact h x y

/-- Exterior multiplication as a morphism out of the tensor product. -/
def mul (M : ModuleCat.{u} R) (i j : ℕ) :
    M.exteriorPower i ⊗ M.exteriorPower j ⟶ M.exteriorPower (i + j) :=
  ofHom (TensorProduct.lift (_root_.exteriorPower.wedge R M i j))

/-- Exterior multiplication on a pure tensor is the wedge product. -/
@[simp]
lemma mul_tmul (M : ModuleCat.{u} R) {i j : ℕ} (x : M.exteriorPower i)
    (y : M.exteriorPower j) :
    mul M i j (x ⊗ₜ y) = _root_.exteriorPower.wedge R M i j x y :=
  (rfl)

/-- In the exterior algebra, exterior multiplication is its algebra product. -/
lemma coe_mul_tmul (M : ModuleCat.{u} R) {i j : ℕ} (x : M.exteriorPower i)
    (y : M.exteriorPower j) :
    Subtype.val (mul M i j (x ⊗ₜ y)) = x.1 * y.1 :=
  (rfl)

/-- Transport between equal exterior degrees leaves the ambient exterior-algebra element
unchanged. -/
@[simp]
lemma coe_eqToHom_apply (M : ModuleCat.{u} R) {i j : ℕ} (h : i = j)
    (x : M.exteriorPower i) :
    Subtype.val (eqToHom (congrArg M.exteriorPower h) x) = x.1 := by
  subst h
  rfl

/-- Exterior multiplication is natural in the module. -/
@[reassoc]
lemma mul_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) (i j : ℕ) :
    (map f i ⊗ₘ map f j) ≫ mul N i j = mul M i j ≫ map f (i + j) := by
  refine MonoidalCategory.tensor_ext fun x y ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.tensorHom_tmul, coe_mul_tmul]
  exact congrArg Subtype.val (_root_.exteriorPower.wedge_map_apply f.hom x y)

/-- Exterior multiplication is associative, with the canonical identification of degrees. -/
@[reassoc]
lemma mul_assoc (M : ModuleCat.{u} R) (i j k : ℕ) :
    (mul M i j ▷ M.exteriorPower k) ≫ mul M (i + j) k =
      (α_ _ _ _).hom ≫ (M.exteriorPower i ◁ mul M j k) ≫ mul M i (j + k) ≫
        eqToHom (congrArg M.exteriorPower (add_assoc i j k).symm) := by
  refine MonoidalCategory.tensor_ext₃' fun x y z ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.whiskerRight_apply, coe_mul_tmul, coe_mul_tmul,
    MonoidalCategory.associator_hom_apply, MonoidalCategory.whiskerLeft_apply,
    coe_eqToHom_apply M (add_assoc i j k).symm, coe_mul_tmul, coe_mul_tmul,
    _root_.mul_assoc]

/-- The inverse degree-zero identification sends a scalar to the corresponding scalar in the
exterior algebra. -/
@[simp]
lemma coe_iso₀_inv_apply (M : ModuleCat.{u} R) (r : R) :
    Subtype.val ((iso₀ M).inv r) = algebraMap R (ExteriorAlgebra R M) r := by
  -- Unwrap the categorical morphism supplied by `LinearEquiv.toModuleIso`.
  change Subtype.val ((_root_.exteriorPower.zeroEquiv R M).symm r) = _
  simp [_root_.exteriorPower.zeroEquiv_symm_apply, Algebra.algebraMap_eq_smul_one]

/-- The degree-zero unit is a left identity for exterior multiplication. -/
@[reassoc]
lemma one_mul (M : ModuleCat.{u} R) (n : ℕ) :
    ((iso₀ M).inv ▷ M.exteriorPower n) ≫ mul M 0 n =
      (λ_ (M.exteriorPower n)).hom ≫ eqToHom (congrArg M.exteriorPower (zero_add n).symm) := by
  refine MonoidalCategory.tensor_ext fun r x ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.whiskerRight_apply, coe_mul_tmul, coe_iso₀_inv_apply,
    MonoidalCategory.leftUnitor_hom_apply, coe_eqToHom_apply M (zero_add n).symm]
  exact (Algebra.smul_def r x.1).symm

/-- The degree-zero unit is a right identity for exterior multiplication. -/
@[reassoc]
lemma mul_one (M : ModuleCat.{u} R) (n : ℕ) :
    (M.exteriorPower n ◁ (iso₀ M).inv) ≫ mul M n 0 =
      (ρ_ (M.exteriorPower n)).hom ≫ eqToHom (congrArg M.exteriorPower (add_zero n).symm) := by
  refine MonoidalCategory.tensor_ext fun x r ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.whiskerLeft_apply, coe_mul_tmul, coe_iso₀_inv_apply,
    MonoidalCategory.rightUnitor_hom_apply, coe_eqToHom_apply M (add_zero n).symm]
  exact (Algebra.commutes r x.1).symm.trans (Algebra.smul_def r x.1).symm

/-- Exterior multiplication is graded commutative, with Koszul sign `(-1)^(i*j)`. -/
@[reassoc]
lemma mul_comm (M : ModuleCat.{u} R) (i j : ℕ) :
    (β_ (M.exteriorPower i) (M.exteriorPower j)).hom ≫ mul M j i =
      (-1 : ℤ) ^ (i * j) •
        (mul M i j ≫ eqToHom (congrArg M.exteriorPower (add_comm i j))) := by
  refine tensor_hom_ext fun x y ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply, MonoidalCategory.braiding_hom_apply, coe_mul_tmul]
  exact (ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := R) y x).trans
    (congrArg (fun z : ExteriorAlgebra R M ↦ (-1 : ℤ) ^ (i * j) • z)
      (coe_eqToHom_apply M (add_comm i j) (mul M i j (mk x ⊗ₜ mk y))).symm)

end ModuleCat.exteriorPower
