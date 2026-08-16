/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Basic
public import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.Algebra.Lie.UniversalEnveloping.Commutation

/-!
# Chevalley commutator relations for Kostant root subgroups

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ`, let `M ≤ V` be a
`U_ℤ`-stable additive subgroup, and let `eᵢ`, `eⱼ`, `eₖ` be distinguished root vectors with
nilpotent images. If

```text
⁅eᵢ, eⱼ⁆ = c • eₖ,   ⁅eᵢ, eₖ⁆ = 0,   ⁅eⱼ, eₖ⁆ = 0
```

for an integer `c` — the situation of two roots `α`, `β` with `α + β` a root but neither
`2α + β` nor `α + 2β` a root, `c` being the Chevalley structure constant `N_{α β}` — then the
root subgroups on the points of `M ⊗ A` satisfy the Chevalley commutator relation

```text
x_α(t) x_β(u) x_α(t)⁻¹ = x_β(u) x_{α+β}(c t u).
```

This is the case of the Chevalley commutator formula in which only one further root subgroup
occurs; in a simply-laced root system every pair of non-proportional roots falls under it or under
the commuting case. The relation holds over every commutative ring `A`, with no factorial
inverted, because it descends from the coefficient-one normal-ordering rule for divided powers.

The general statement about integral nilpotent exponentials is
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq`; this file only supplies the
Lie-theoretic hypotheses and transports the identity to the root subgroups in
`LinearMap.GeneralLinearGroup`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupPoints`: root subgroups of
  commuting root vectors commute.
* `kostantRootSubgroupPoints_mul_kostantRootSubgroupPoints_of_lie_eq`:
  the normal-ordering relation, for any `𝔾ₐ`-point carrying the parameter `c * t * u`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_lie_eq`: its conjugation
  form.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_lie_eq'`: the conjugation
  form with that point written out.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupPoints`: the classical
  group-commutator form.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of the enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [CommRing A] [Algebra ℤ A]

private theorem gaPointParamMul_zpow_param
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (c : ℤ) :
    Multiplicative.toAdd
        (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)
          ((AdditiveGroup.gaPointParamMul f g) ^ c)) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)) := by
  simp only [map_zpow, AdditiveGroup.gaPointsMulEquiv_gaPointParamMul,
    toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul]

/-- **The degenerate Chevalley commutator relation for Kostant root subgroups.** Root subgroups
attached to commuting root vectors commute. For a root system this is the case of two roots whose
sum is not a root and which are not opposite. -/
theorem commute_kostantRootSubgroupPoints {i j : ι} (hij : ⁅e i, e j⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Commute (kostantRootSubgroupPoints e h ρ M hM i hi f)
      (kostantRootSubgroupPoints e h ρ M hM j hj g) := by
  have hcomm : Commute (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) :=
    commute_map_ι_of_lie_eq_zero ρ hij
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  exact commute_baseChangeExp M hcomm _ _ _ _

/-- **The Chevalley commutator relation for Kostant root subgroups.** Suppose the distinguished
root vectors satisfy `⁅eᵢ, eⱼ⁆ = c • eₖ` with `eₖ` central for both, and let `w` be any
`𝔾ₐ`-point whose parameter is `c` times the product of the parameters of `f` and `g`. Then

```text
xᵢ(f) xⱼ(g) = xⱼ(g) xₖ(w) xᵢ(f).
```

The hypotheses are exactly the class-two case of the Chevalley commutator formula: `α + β` is a
root, while `2α + β` and `α + 2β` are not. -/
theorem kostantRootSubgroupPoints_mul_kostantRootSubgroupPoints_of_lie_eq {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g w : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hw : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) w) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk w *
        kostantRootSubgroupPoints e h ρ M hM i hi f := by
  -- The commutator of the first two root vectors is `c` times the third.
  have hxy : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) *
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j)) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j)) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) +
        c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) := by
    have hb := map_ι_mul_map_ι_sub_eq_map_ι_lie ρ (e i) (e j)
    rw [hij, map_zsmul, map_zsmul] at hb
    exact sub_eq_iff_eq_add'.mp hb
  -- The third root vector commutes with the other two.
  have hcxz : Commute (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) :=
    commute_map_ι_of_lie_eq_zero ρ hik
  have hcyz : Commute (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) :=
    commute_map_ι_of_lie_eq_zero ρ hjk
  -- Stability of `M` under the divided powers of the scaled commutator.
  have hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) • v ∈ M := by
    intro n v hv
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv) _
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  rw [hw, ← baseChangeExp_zsmul_left c M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv) hMz hk]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy (Commute.smul_right hcxz c)
    (Commute.smul_right hcyz c) hi hj _ _ hMz _ _

/-- The Chevalley commutator relation with the third `𝔾ₐ`-point written out: it is the point whose
parameter is `c` times the product of the parameters of `f` and `g`. -/
theorem kostantRootSubgroupPoints_mul_kostantRootSubgroupPoints_of_lie_eq' {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointParamMul f g) ^ c) *
        kostantRootSubgroupPoints e h ρ M hM i hi f :=
  kostantRootSubgroupPoints_mul_kostantRootSubgroupPoints_of_lie_eq
    e h ρ M hM hij hik hjk hi hj hk f g _ (gaPointParamMul_zpow_param f g c)

/-- The conjugation form of the Chevalley commutator relation: conjugating the root subgroup of
`eⱼ` by the root subgroup of `eᵢ` multiplies it by the root subgroup of `eₖ`, at the parameter
`c * t * u`. -/
theorem kostantRootSubgroupPoints_conj_of_lie_eq {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g w : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hw : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) w) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk w := by
  rw [kostantRootSubgroupPoints_mul_kostantRootSubgroupPoints_of_lie_eq
    e h ρ M hM hij hik hjk hi hj hk f g w hw, mul_inv_cancel_right]

/-- The conjugation form of the Chevalley commutator relation with the third `𝔾ₐ`-point written
out: it is the point whose parameter is `c` times the product of the parameters of `f` and `g`. -/
theorem kostantRootSubgroupPoints_conj_of_lie_eq' {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointParamMul f g) ^ c) :=
  kostantRootSubgroupPoints_conj_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g _
    (gaPointParamMul_zpow_param f g c)

/-- **The Chevalley commutator relation for Kostant root subgroups, in group-commutator form.**
Under the class-two bracket hypotheses, the commutator of the first two root-subgroup points is
the third point at parameter `c * t * u`. -/
theorem commutatorElement_kostantRootSubgroupPoints {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g w : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hw : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) w) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk w := by
  have hcomm := commute_kostantRootSubgroupPoints e h ρ M hM hjk hj hk g w
  rw [commutatorElement_def,
    kostantRootSubgroupPoints_conj_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g w hw,
    hcomm.eq, mul_assoc]
  simp

/-- The group-commutator form with the resulting `𝔾ₐ`-point expressed using parameter
multiplication and the integer power operation. -/
theorem commutatorElement_kostantRootSubgroupPoints' {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk
        ((AdditiveGroup.gaPointParamMul f g) ^ c) :=
  commutatorElement_kostantRootSubgroupPoints e h ρ M hM hij hik hjk hi hj hk f g _ (by
    exact gaPointParamMul_zpow_param f g c)

end TauCeti.UniversalEnvelopingAlgebra
