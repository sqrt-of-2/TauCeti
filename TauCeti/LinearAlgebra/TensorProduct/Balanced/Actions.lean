/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# Outer actions on balanced tensor products

If the right `A`-module `M` also carries a commuting left `B`-action, then
`M ⊗[A] N` inherits that action on its first factor. A commuting action on `N`
similarly acts on the second factor. The two induced actions commute. Taking the
second acting semiring to be `Cᵐᵒᵖ` gives the outer actions of the tensor product
of a `(B,A)`-bimodule and an `(A,C)`-bimodule.

The actions are packaged as homomorphisms into ground-ring linear endomorphisms.
The associated module structures are opt-in definitions, not global instances:
when both factors carry an action of the same semiring, the two actions need not
agree. Pure-tensor formulas and equivariance of tensor maps characterize them
without exposing the quotient presentation.

This is the ordinary bimodule tensor construction used in Keller,
*Deriving DG categories*, Section 6.1. It uses Mathlib's
`DistribSMul.toLinearMap` and the existing balanced tensor map.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable {k A M N : Type*} [CommRing k] [Semiring A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]

section Left

variable (B : Type*) [Semiring B] [Module B M]
  [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M]

/-- A commuting action on the first factor descends to the balanced tensor product. -/
def leftAction : B →+* Module.End k (BalancedTensorProduct k A M N) where
  toFun b := map (DistribSMul.toLinearMap k M b) LinearMap.id
    (fun a m ↦ by simpa using smul_comm b (op a) m) (fun _ _ ↦ rfl)
  map_zero' := hom_ext fun m n ↦ by simp
  map_one' := hom_ext fun m n ↦ by simp
  map_add' b b' := hom_ext fun m n ↦ by simp [add_smul, add_tmul]
  map_mul' b b' := hom_ext fun m n ↦ by simp [mul_smul]

@[simp]
theorem leftAction_tmul (b : B) (m : M) (n : N) :
    leftAction (k := k) (A := A) (N := N) B b (tmul k A m n) =
      tmul k A (b • m) n := by
  simp [leftAction]

/-- The first-factor module structure. Install locally with `letI := leftModule ...`. -/
abbrev leftModule : Module B (BalancedTensorProduct k A M N) :=
  Module.compHom _ (leftAction (k := k) (A := A) (M := M) (N := N) B)

/-- Under the first-factor module structure, scalar multiplication acts on the first tensor. -/
@[simp]
theorem left_smul_tmul (b : B) (m : M) (n : N) :
    letI := leftModule (k := k) (A := A) (M := M) (N := N) B
    b • tmul k A m n = tmul k A (b • m) n := by
  exact leftAction_tmul B b m n

/-- The first-factor action commutes with the ground-ring action. -/
theorem leftSMulCommClass :
    letI := leftModule (k := k) (A := A) (M := M) (N := N) B
    SMulCommClass B k (BalancedTensorProduct k A M N) := by
  let := leftModule (k := k) (A := A) (M := M) (N := N) B
  exact ⟨fun b r x ↦ (leftAction B b).map_smul r x⟩

/-- A ground-ring scalar tower on the first factor descends to the tensor product. -/
theorem leftIsScalarTower [SMul k B] [IsScalarTower k B M] :
    letI := leftModule (k := k) (A := A) (M := M) (N := N) B
    IsScalarTower k B (BalancedTensorProduct k A M N) := by
  let := leftModule (k := k) (A := A) (M := M) (N := N) B
  refine ⟨fun r b x ↦ ?_⟩
  induction x using induction_on with
  | ht m n => simp [left_smul_tmul, smul_assoc]
  | ha x y hx hy => simp [smul_add, hx, hy]

end Left

section Right

variable (C : Type*) [Semiring C] [Module C N]
  [SMulCommClass C k N] [SMulCommClass C A N]

/-- A commuting action on the second factor descends to the balanced tensor product. -/
def rightAction : C →+* Module.End k (BalancedTensorProduct k A M N) where
  toFun c := map LinearMap.id (DistribSMul.toLinearMap k N c)
    (fun _ _ ↦ rfl) (fun a n ↦ by simpa using smul_comm c a n)
  map_zero' := hom_ext fun m n ↦ by simp
  map_one' := hom_ext fun m n ↦ by simp
  map_add' c c' := hom_ext fun m n ↦ by simp [add_smul, tmul_add]
  map_mul' c c' := hom_ext fun m n ↦ by simp [mul_smul]

@[simp]
theorem rightAction_tmul (c : C) (m : M) (n : N) :
    rightAction (k := k) (A := A) (M := M) C c (tmul k A m n) =
      tmul k A m (c • n) := by
  simp [rightAction]

/-- The second-factor module structure. For a right action use `Cᵐᵒᵖ` as the semiring. -/
abbrev rightModule : Module C (BalancedTensorProduct k A M N) :=
  Module.compHom _ (rightAction (k := k) (A := A) (M := M) (N := N) C)

/-- Under the second-factor module structure, scalar multiplication acts on the second tensor. -/
@[simp]
theorem right_smul_tmul (c : C) (m : M) (n : N) :
    letI := rightModule (k := k) (A := A) (M := M) (N := N) C
    c • tmul k A m n = tmul k A m (c • n) := by
  exact rightAction_tmul C c m n

/-- The second-factor action commutes with the ground-ring action. -/
theorem rightSMulCommClass :
    letI := rightModule (k := k) (A := A) (M := M) (N := N) C
    SMulCommClass C k (BalancedTensorProduct k A M N) := by
  let := rightModule (k := k) (A := A) (M := M) (N := N) C
  exact ⟨fun c r x ↦ (rightAction C c).map_smul r x⟩

/-- A ground-ring scalar tower on the second factor descends to the tensor product. -/
theorem rightIsScalarTower [SMul k C] [IsScalarTower k C N] :
    letI := rightModule (k := k) (A := A) (M := M) (N := N) C
    IsScalarTower k C (BalancedTensorProduct k A M N) := by
  let := rightModule (k := k) (A := A) (M := M) (N := N) C
  refine ⟨fun r c x ↦ ?_⟩
  induction x using induction_on with
  | ht m n => simp [right_smul_tmul, smul_assoc]
  | ha x y hx hy => simp [smul_add, hx, hy]

end Right

section Both

variable (B C : Type*) [Semiring B] [Semiring C]
  [Module B M] [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M]
  [Module C N] [SMulCommClass C k N] [SMulCommClass C A N]

/-- The two outer actions commute as ground-ring linear endomorphisms. -/
theorem leftAction_comp_rightAction (b : B) (c : C) :
    (leftAction (k := k) (A := A) (M := M) (N := N) B b).comp (rightAction C c) =
      (rightAction C c).comp (leftAction B b) := by
  apply hom_ext
  intro m n
  simp

/-- Tensoring bimodules produces commuting outer actions. -/
theorem outerSMulCommClass :
    letI := leftModule (k := k) (A := A) (M := M) (N := N) B
    letI := rightModule (k := k) (A := A) (M := M) (N := N) C
    SMulCommClass B C (BalancedTensorProduct k A M N) := by
  let := leftModule (k := k) (A := A) (M := M) (N := N) B
  let := rightModule (k := k) (A := A) (M := M) (N := N) C
  exact ⟨fun b c x ↦ LinearMap.congr_fun (leftAction_comp_rightAction B C b c) x⟩

end Both

section Map

variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module A N']
  (f : M →ₗ[k] M') (g : N →ₗ[k] N')
  (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
  (hg : ∀ (a : A) n, g (a • n) = a • g n)

/-- Tensor maps intertwine the first-factor actions when the first map is equivariant. -/
theorem map_comp_leftAction (B : Type*) [Semiring B]
    [Module B M] [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M]
    [Module B M'] [SMulCommClass B k M'] [SMulCommClass B Aᵐᵒᵖ M']
    (hB : ∀ (b : B) m, f (b • m) = b • f m) (b : B) :
    (map f g hf hg).comp (leftAction B b) =
      (leftAction B b).comp (map f g hf hg) := by
  apply hom_ext
  intro m n
  simp [hB]

/-- Tensor maps intertwine the second-factor actions when the second map is equivariant. -/
theorem map_comp_rightAction (C : Type*) [Semiring C]
    [Module C N] [SMulCommClass C k N] [SMulCommClass C A N]
    [Module C N'] [SMulCommClass C k N'] [SMulCommClass C A N']
    (hC : ∀ (c : C) n, g (c • n) = c • g n) (c : C) :
    (map f g hf hg).comp (rightAction C c) =
      (rightAction C c).comp (map f g hf hg) := by
  apply hom_ext
  intro m n
  simp [hC]

end Map

end TauCeti.BalancedTensorProduct
