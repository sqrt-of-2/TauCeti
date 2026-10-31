/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Character
public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Current.CentralExtension
public import TauCeti.Algebra.Lie.Current.Topology
public import TauCeti.Algebra.Lie.Extension.Topology

/-!
# Canonical splittings over nonnegative-order currents

The currents of order at least `n ≥ 0` form a Lie subalgebra `a_n`. The residue cocycle
vanishes on this subalgebra, so the zero-central-coordinate section is a Lie homomorphism.
The preimage of `a_n` in the residue extension is canonically the direct product `a_n × R`.
These splittings agree under inclusion of higher-order currents and are continuous.

The central-coordinate character, scaled by any `a : R`, kills `a_n` and takes the value
`a` on the distinguished central generator. It specifies the one-dimensional representation
used to induce vacuum and congruence modules. All constructions include `n = 0`, arbitrary
invariant symmetric forms (including zero), and arbitrary commutative coefficient rings.

The residue convention is `Res(f dg) Φ(x,y)`, so the affine level form is `κ = -Φ`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1 and §3.2.
-/

public section

noncomputable section

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The Lie subalgebra of currents of order at least the nonnegative integer `n`. -/
def orderLieSubalgebra (n : ℕ) : LieSubalgebra R (currentAlgebra R L) where
  toSubmodule := orderSubmodule R L n
  lie_mem' {u v} hu hv := orderSubmodule_antitone R L (by omega : (n : ℤ) ≤ n + n)
    (lie_mem_orderSubmodule R L hu hv)

/-- The underlying submodule of `a_n` is the order submodule. -/
@[simp]
theorem orderLieSubalgebra_toSubmodule (n : ℕ) :
    (orderLieSubalgebra R L n).toSubmodule = orderSubmodule R L n :=
  (rfl)

/-- Membership in `a_n` is the order condition. -/
@[simp]
theorem mem_orderLieSubalgebra (n : ℕ) (u : currentAlgebra R L) :
    u ∈ orderLieSubalgebra R L n ↔ u ∈ orderSubmodule R L n :=
  (Iff.rfl)

/-- The current Lie subalgebras decrease with the order. -/
theorem orderLieSubalgebra_antitone : Antitone (orderLieSubalgebra R L) :=
  fun m n h u hu ↦ orderSubmodule_antitone R L (by exact_mod_cast h) hu

variable {R L} (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "C" => currentAlgebra R L
local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "E" => ofTwoCocycle c

/-- The preimage `a_n ⊕ R K` of the order Lie subalgebra in the residue extension. -/
def orderExtensionLieSubalgebra (n : ℕ) : LieSubalgebra R E :=
  (orderLieSubalgebra R L n).comap (ofTwoCocycle.proj c)

/-- An element lies in the central preimage exactly when its projection has the required order. -/
@[simp]
theorem mem_orderExtensionLieSubalgebra (n : ℕ) (v : E) :
    v ∈ orderExtensionLieSubalgebra Φ hΦ hΦs n ↔
      ofTwoCocycle.proj c v ∈ orderLieSubalgebra R L n :=
  (Iff.rfl)

/-- The central preimages decrease with the order. -/
theorem orderExtensionLieSubalgebra_antitone :
    Antitone (orderExtensionLieSubalgebra Φ hΦ hΦs) :=
  fun _ _ h _ hu ↦ orderLieSubalgebra_antitone R L h hu

/-- The canonical splitting of the central preimage as a direct product of Lie algebras. -/
def orderExtensionEquiv (n : ℕ) :
    (orderLieSubalgebra R L n × R) ≃ₗ⁅R⁆ orderExtensionLieSubalgebra Φ hΦ hΦs n where
  toFun p := ⟨ofProd c (p.1, (TrivialLieModule.equiv R C R).symm p.2), by
    simp⟩
  invFun v := (⟨ofTwoCocycle.proj c v,
    (mem_orderExtensionLieSubalgebra Φ hΦ hΦs n v).mp v.property⟩,
    TrivialLieModule.equiv R C R ((ofProd c).symm v).2)
  left_inv p := by simp
  right_inv v := Subtype.ext (by simp [ofTwoCocycle.proj_apply])
  map_add' p q := Subtype.ext (by simp [← of_add])
  map_smul' r p := Subtype.ext (by simp [← of_smul, -smul_eq_mul])
  map_lie' {p q} := by
    apply Subtype.ext
    simp only [LieSubalgebra.coe_bracket, bracket_ofTwoCocycle, Equiv.symm_apply_apply,
      trivial_lie_zero, sub_zero, add_zero, twoCocycleOfBilinear_coe,
      LieModule.Cohomology.twoCochain_val_apply, twoCochainOfBilinear_apply_apply,
      LieAlgebra.Prod.bracket_apply]
    rw [residuePairing_eq_zero_of_mem_orderSubmodule_zero R L Φ
      (orderSubmodule_antitone R L (Int.natCast_nonneg n) p.1.property)
      (orderSubmodule_antitone R L (Int.natCast_nonneg n) q.1.property)]
    simp [LieRing.of_associative_ring_bracket, mul_comm]

/-- Forward coordinates of the canonical splitting. -/
@[simp]
theorem coe_orderExtensionEquiv (n : ℕ) (p : orderLieSubalgebra R L n × R) :
    (orderExtensionEquiv Φ hΦ hΦs n p : E) =
      ofProd c (p.1, (TrivialLieModule.equiv R C R).symm p.2) :=
  (rfl)

/-- Inverse coordinates of the canonical splitting. -/
@[simp]
theorem orderExtensionEquiv_symm_apply (n : ℕ)
    (v : orderExtensionLieSubalgebra Φ hΦ hΦs n) :
    (orderExtensionEquiv Φ hΦ hΦs n).symm v =
      (⟨ofTwoCocycle.proj c v,
          (mem_orderExtensionLieSubalgebra Φ hΦ hΦs n v).mp v.property⟩,
        TrivialLieModule.equiv R C R ((ofProd c).symm v).2) :=
  (rfl)

/-- The canonical Lie section over currents of nonnegative order, with central coordinate zero. -/
def orderSection (n : ℕ) : orderLieSubalgebra R L n →ₗ⁅R⁆ E :=
  (orderExtensionLieSubalgebra Φ hΦ hΦs n).incl.comp
    ((orderExtensionEquiv Φ hΦ hΦs n).toLieHom.comp
      (LieHom.inl R (orderLieSubalgebra R L n) R))

/-- The section puts zero in the central coordinate. -/
@[simp]
theorem orderSection_apply (n : ℕ) (u : orderLieSubalgebra R L n) :
    orderSection Φ hΦ hΦs n u = ofProd c (u, 0) := by
  simp [orderSection]

/-- Canonical sections agree under inclusion of higher-order currents. -/
theorem orderSection_inclusion {m n : ℕ} (h : n ≤ m) (u : orderLieSubalgebra R L m) :
    orderSection Φ hΦ hΦs n
      (LieSubalgebra.inclusion (orderLieSubalgebra_antitone R L h) u) =
        orderSection Φ hΦ hΦs m u := by
  simp

/-- The central-coordinate character with central value `a`, killing the order currents. -/
def orderCharacter (a : R) (n : ℕ) :
    LieCharacter R (orderExtensionLieSubalgebra Φ hΦ hΦs n) :=
  letI : IsLieAbelian R := ⟨fun x y ↦ by
    simp [LieRing.of_associative_ring_bracket, mul_comm]⟩
  ((lieCharacterEquivLinearDual (R := R) (L := R)).symm (a • LinearMap.id)).comp
    ((LieHom.snd R (orderLieSubalgebra R L n) R).comp
      (orderExtensionEquiv Φ hΦ hΦs n).symm.toLieHom)

/-- The inducing character is `a` times the central coordinate. -/
@[simp]
theorem orderCharacter_apply (a : R) (n : ℕ)
    (v : orderExtensionLieSubalgebra Φ hΦ hΦs n) :
    orderCharacter Φ hΦ hΦs a n v =
      a * TrivialLieModule.equiv R C R ((ofProd c).symm v).2 :=
  (rfl)

/-- The distinguished central generator belongs to every central preimage. -/
theorem centralElement_mem_orderExtensionLieSubalgebra (n : ℕ) :
    centralElement Φ hΦ hΦs ∈ orderExtensionLieSubalgebra Φ hΦ hΦs n := by
  rw [mem_orderExtensionLieSubalgebra, ofTwoCocycle.proj_apply,
    ofProd_symm_centralElement]
  exact zero_mem _

/-- The canonical Lie section is continuous for the induced order topology. -/
theorem continuous_orderSection (n : ℕ) : Continuous (orderSection Φ hΦ hΦs n) := by
  convert (ofTwoCocycle.inl c).continuous.comp
    (continuous_subtype_val : Continuous fun u : orderLieSubalgebra R L n ↦ (u : C)) using 1
  ext u
  simp

/-- With discrete scalars, the splitting is continuous for the product and subspace topologies. -/
theorem continuous_orderExtensionEquiv [TopologicalSpace R] [DiscreteTopology R] (n : ℕ) :
    Continuous (orderExtensionEquiv Φ hΦ hΦs n) := by
  apply Continuous.subtype_mk
  exact ofTwoCocycle.continuous_iff.mpr
    ⟨continuous_subtype_val.comp continuous_fst,
      (IsLocallyConstant.of_discrete (TrivialLieModule.equiv R C R).symm).comp_continuous
        continuous_snd⟩

/-- The inverse splitting is continuous for any topology on the scalar target: its central
coordinate is locally constant. -/
theorem continuous_orderExtensionEquiv_symm [TopologicalSpace R] (n : ℕ) :
    Continuous (orderExtensionEquiv Φ hΦ hΦs n).symm :=
  (((ofTwoCocycle.continuous_proj c).comp continuous_subtype_val).subtype_mk _).prodMk
    (((ofTwoCocycle.isLocallyConstant_snd c).comp_continuous continuous_subtype_val).comp
      (TrivialLieModule.equiv R C R)).continuous

end TauCeti.CurrentAlgebra
