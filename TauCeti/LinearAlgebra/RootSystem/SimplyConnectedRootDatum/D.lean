/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD

/-!
# The simply connected root datum of type `Dₙ`

This file turns the classical integral roots of type `Dₙ` into the pinned simply connected root
datum required by the root-systems roadmap. Both lattices are `Fin n → ℤ`: the character lattice
is written in the fundamental-weight basis and the cocharacter lattice in the simple-coroot basis.
For a classical root `x`, its coroot is its already-constructed expansion in the Bourbaki simple
roots, while its character is the list of dot products with those simple roots.

The roots are indexed by `Fin (2 * n * (n - 1))`, using the enumeration in
`TauCeti.DynkinType.typeDRootEquiv`; its first `n` entries are the Bourbaki simple roots. Reflection
is transported from the classical reflection permutation. The pinned base realizes
`CartanMatrix.D n`, and its coroots are the standard basis, hence span the cocharacter lattice.

## Main definitions and results

* `TauCeti.DynkinType.typeDSimplyConnectedRootDatum` is the pinned integral datum of type `Dₙ`.
* `TauCeti.DynkinType.typeDSimplyConnectedBase` is its Bourbaki-numbered base.
* `TauCeti.DynkinType.hasCartanType_typeDSimplyConnectedRootDatum` identifies its Cartan type.
* `TauCeti.DynkinType.corootSpan_typeDSimplyConnectedRootDatum_eq_top` proves the simply connected
  lattice condition.

## References

The coordinates and node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IV, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section 12.1.
This completes the `Dₙ` branch of “a named datum per valid type” in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

public section

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

private instance : (dotProductBilin ℤ ℤ :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] ℤ).IsPerfPair := by
  change (dotProductEquiv ℤ (Fin n)).toLinearMap.IsPerfPair
  infer_instance

/-! ## Roots, coroots, and reflections -/

private def typeDCharacterRoot (n : ℕ) (hn : 4 ≤ n) (x : TypeDRoot n) : Fin n → ℤ :=
  fun i => x.1 ⬝ᵥ typeDSimpleRoot n hn i

private def typeDCoroot (n : ℕ) (hn : 4 ≤ n) (x : TypeDRoot n) : Fin n → ℤ :=
  typeDSimpleRootCoordinates n hn x

private lemma sum_smul_typeDCoroot (hn : 4 ≤ n) (x : TypeDRoot n) :
    ∑ i, typeDCoroot n hn x i • typeDSimpleRoot n hn i = x.1 :=
  sum_smul_typeDSimpleRootCoordinates hn x

private lemma typeDCharacterRoot_dot_coroot (hn : 4 ≤ n) (x y : TypeDRoot n) :
    typeDCharacterRoot n hn x ⬝ᵥ typeDCoroot n hn y = x.1 ⬝ᵥ y.1 := by
  calc
    typeDCharacterRoot n hn x ⬝ᵥ typeDCoroot n hn y =
        ∑ i, typeDCoroot n hn y i * (x.1 ⬝ᵥ typeDSimpleRoot n hn i) := by
      simp [typeDCharacterRoot, typeDCoroot, dotProduct, mul_comm]
    _ = x.1 ⬝ᵥ ∑ i, typeDCoroot n hn y i • typeDSimpleRoot n hn i := by
      rw [dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
    _ = x.1 ⬝ᵥ y.1 := by
      rw [sum_smul_typeDCoroot hn y]

private lemma typeDCoroot_injective (hn : 4 ≤ n) :
    Injective (typeDCoroot n hn) := by
  intro x y h
  apply Subtype.ext
  rw [← sum_smul_typeDCoroot hn x, ← sum_smul_typeDCoroot hn y, h]

private lemma typeDCharacterRoot_injective (hn : 4 ≤ n) :
    Injective (typeDCharacterRoot n hn) := by
  intro x y h
  apply Subtype.ext
  have horth : ∀ i, (x.1 - y.1) ⬝ᵥ typeDSimpleRoot n hn i = 0 := by
    intro i
    have hi := congrFun h i
    simpa only [typeDCharacterRoot, sub_dotProduct, sub_eq_zero] using hi
  have hreconstruct :
      ∑ i : Fin n, (typeDCoroot n hn x i - typeDCoroot n hn y i) •
          typeDSimpleRoot n hn i = x.1 - y.1 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    rw [sum_smul_typeDCoroot hn x, sum_smul_typeDCoroot hn y]
  have hself : (x.1 - y.1) ⬝ᵥ (x.1 - y.1) = 0 := by
    calc
      (x.1 - y.1) ⬝ᵥ (x.1 - y.1) =
          (x.1 - y.1) ⬝ᵥ ∑ i, (typeDCoroot n hn x i - typeDCoroot n hn y i) •
            typeDSimpleRoot n hn i := congrArg ((x.1 - y.1) ⬝ᵥ ·) hreconstruct.symm
      _ = 0 := by
        rw [dotProduct_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [dotProduct_smul, horth i, smul_zero]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hself)

private noncomputable def typeDReflectionPerm (n : ℕ) (hn : 4 ≤ n)
    (k : Fin (2 * n * (n - 1))) : Equiv.Perm (Fin (2 * n * (n - 1))) :=
  (typeDRootEquiv n hn).trans
    ((typeDRootReflectionEquiv (typeDRootEquiv n hn k)).trans (typeDRootEquiv n hn).symm)

private lemma typeDRootEquiv_typeDReflectionPerm (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    typeDRootEquiv n hn (typeDReflectionPerm n hn k l) =
      typeDRootReflection (typeDRootEquiv n hn k) (typeDRootEquiv n hn l) := by
  simp [typeDReflectionPerm]

private lemma typeDReflectionPerm_root (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    typeDCharacterRoot n hn (typeDRootEquiv n hn l) -
        (typeDCharacterRoot n hn (typeDRootEquiv n hn l) ⬝ᵥ
          typeDCoroot n hn (typeDRootEquiv n hn k)) •
          typeDCharacterRoot n hn (typeDRootEquiv n hn k) =
      typeDCharacterRoot n hn (typeDRootEquiv n hn (typeDReflectionPerm n hn k l)) := by
  rw [typeDCharacterRoot_dot_coroot, typeDRootEquiv_typeDReflectionPerm]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, typeDCharacterRoot, typeDRootReflection_val,
    sub_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma typeDReflectionPerm_coroot (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    typeDCoroot n hn (typeDRootEquiv n hn l) -
        (typeDCharacterRoot n hn (typeDRootEquiv n hn k) ⬝ᵥ
          typeDCoroot n hn (typeDRootEquiv n hn l)) •
          typeDCoroot n hn (typeDRootEquiv n hn k) =
      typeDCoroot n hn (typeDRootEquiv n hn (typeDReflectionPerm n hn k l)) := by
  rw [typeDCharacterRoot_dot_coroot, typeDRootEquiv_typeDReflectionPerm]
  apply funext
  intro i
  apply (linearIndependent_typeDSimpleRoot hn).eq_coords_of_eq
  simp only [Pi.sub_apply, Pi.smul_apply, sub_smul]
  simp_rw [smul_eq_mul]
  simp_rw [mul_smul]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.smul_sum]
  rw [sum_smul_typeDCoroot hn, sum_smul_typeDCoroot hn, sum_smul_typeDCoroot hn]
  simp [typeDRootReflection_val, dotProduct_comm]

/-- The pinned simply connected root datum of type `Dₙ`.

Both lattices are `Fin n → ℤ`. The character lattice uses fundamental-weight coordinates, the
cocharacter lattice uses simple-coroot coordinates, and the classical enumeration places the
Bourbaki simple roots first. -/
noncomputable def typeDSimplyConnectedRootDatum (n : ℕ) (hn : 4 ≤ n) :
    RootDatum (Fin (2 * n * (n - 1))) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := dotProductBilin ℤ ℤ
  root := ⟨fun k => typeDCharacterRoot n hn (typeDRootEquiv n hn k),
    (typeDCharacterRoot_injective hn).comp (typeDRootEquiv n hn).injective⟩
  coroot := ⟨fun k => typeDCoroot n hn (typeDRootEquiv n hn k),
    (typeDCoroot_injective hn).comp (typeDRootEquiv n hn).injective⟩
  root_coroot_two k :=
    (typeDCharacterRoot_dot_coroot hn (typeDRootEquiv n hn k)
      (typeDRootEquiv n hn k)).trans (typeDRootEquiv n hn k).2
  reflectionPerm := typeDReflectionPerm n hn
  reflectionPerm_root := typeDReflectionPerm_root hn
  reflectionPerm_coroot := typeDReflectionPerm_coroot hn

private lemma root_typeDSimplyConnectedRootDatum (hn : 4 ≤ n)
    (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).root k =
      typeDCharacterRoot n hn (typeDRootEquiv n hn k) := rfl

private lemma coroot_typeDSimplyConnectedRootDatum (hn : 4 ≤ n)
    (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).coroot k =
      typeDCoroot n hn (typeDRootEquiv n hn k) := rfl

private lemma typeDCoroot_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    typeDCoroot n hn (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) = Pi.single i 1 :=
  typeDSimpleRootCoordinates_typeDRootEquiv_apply_typeDSimpleIndex hn i

/-- The simple roots of the pinned type `Dₙ` datum are the rows of its Cartan matrix. -/
@[simp] theorem root_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) =
      fun j => CartanMatrix.D n i j := by
  rw [root_typeDSimplyConnectedRootDatum]
  change (fun j => (typeDRootEquiv n hn (typeDSimpleIndex n hn i)).1 ⬝ᵥ
    typeDSimpleRoot n hn j) = _
  rw [typeDRootEquiv_apply_typeDSimpleIndex]
  funext j
  exact typeDSimpleRoot_dotProduct hn i j

/-- The simple coroots of the pinned type `Dₙ` datum are the standard basis. -/
@[simp] theorem coroot_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) =
      Pi.single i 1 := by
  rw [coroot_typeDSimplyConnectedRootDatum]
  exact typeDSimpleRootCoordinates_typeDRootEquiv_apply_typeDSimpleIndex hn i

/-! ## The pinned base -/

private def typeDSimpleSupport (n : ℕ) (hn : 4 ≤ n) :
    Finset (Fin (2 * n * (n - 1))) :=
  Finset.univ.map ⟨typeDSimpleIndex n hn, typeDSimpleIndex_injective hn⟩

private lemma mem_typeDSimpleSupport (hn : 4 ≤ n) {k : Fin (2 * n * (n - 1))} :
    k ∈ typeDSimpleSupport n hn ↔ (k : ℕ) < n := by
  constructor
  · rintro hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hk
    simp
  · intro hk
    exact Finset.mem_map.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

private lemma coe_typeDSimpleSupport (hn : 4 ≤ n) :
    (typeDSimpleSupport n hn : Set (Fin (2 * n * (n - 1)))) =
      range (typeDSimpleIndex n hn) := by
  simp [typeDSimpleSupport]

private lemma sum_zsmul_mem_closure_of_nonneg {M : Type*} [AddCommGroup M]
    (f : Fin n → M) (c : Fin n → ℤ) (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i • f i ∈ AddSubmonoid.closure (range f) := by
  apply AddSubmonoid.sum_mem
  intro i _
  have hcoe : c i = ((c i).toNat : ℤ) := (Int.toNat_of_nonneg (hc i)).symm
  rw [hcoe]
  simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using
    _root_.nsmul_mem (AddSubmonoid.subset_closure (mem_range_self i)) (c i).toNat

private lemma root_eq_sum_typeDCoroot_smul_simpleRoot (hn : 4 ≤ n) (x : TypeDRoot n) :
    typeDCharacterRoot n hn x =
      ∑ i, typeDCoroot n hn x i •
        typeDCharacterRoot n hn (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) := by
  funext j
  simp only [typeDCharacterRoot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [typeDRootEquiv_apply_typeDSimpleIndex]
  calc
    x.1 ⬝ᵥ typeDSimpleRoot n hn j =
        (∑ i, typeDCoroot n hn x i • typeDSimpleRoot n hn i) ⬝ᵥ
          typeDSimpleRoot n hn j :=
      congrArg (· ⬝ᵥ typeDSimpleRoot n hn j) (sum_smul_typeDCoroot hn x).symm
    _ = _ := by
      rw [sum_dotProduct]
      simp only [smul_dotProduct, smul_eq_mul]

private lemma coroot_eq_sum_typeDCoroot_smul_single (hn : 4 ≤ n) (x : TypeDRoot n) :
    typeDCoroot n hn x = ∑ i, typeDCoroot n hn x i • Pi.single i 1 := by
  funext j
  classical
  simp [Pi.single_apply]

private lemma coroot_eq_sum_typeDCoroot_smul_simpleCoroot (hn : 4 ≤ n) (x : TypeDRoot n) :
    typeDCoroot n hn x =
      ∑ i, typeDCoroot n hn x i •
        typeDCoroot n hn (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) := by
  calc
    typeDCoroot n hn x = ∑ i, typeDCoroot n hn x i • Pi.single i 1 :=
      coroot_eq_sum_typeDCoroot_smul_single hn x
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [typeDCoroot_typeDSimpleIndex]

private lemma typeDCharacterRoot_mem_simpleClosure_or_neg (hn : 4 ≤ n) (x : TypeDRoot n) :
    typeDCharacterRoot n hn x ∈ AddSubmonoid.closure
        (range fun i => typeDCharacterRoot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i))) ∨
      -typeDCharacterRoot n hn x ∈ AddSubmonoid.closure
        (range fun i => typeDCharacterRoot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i))) := by
  rcases typeDSimpleRootCoordinates_nonnegative_or_nonpositive hn x with hpos | hneg
  · left
    rw [root_eq_sum_typeDCoroot_smul_simpleRoot]
    exact sum_zsmul_mem_closure_of_nonneg _ _ hpos
  · right
    rw [root_eq_sum_typeDCoroot_smul_simpleRoot, ← Finset.sum_neg_distrib]
    simp_rw [← neg_smul]
    exact sum_zsmul_mem_closure_of_nonneg _ _ fun i => neg_nonneg.mpr (hneg i)

private lemma typeDCoroot_mem_simpleClosure_or_neg (hn : 4 ≤ n) (x : TypeDRoot n) :
    typeDCoroot n hn x ∈ AddSubmonoid.closure
        (range fun i => typeDCoroot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i))) ∨
      -typeDCoroot n hn x ∈ AddSubmonoid.closure
        (range fun i => typeDCoroot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i))) := by
  rcases typeDSimpleRootCoordinates_nonnegative_or_nonpositive hn x with hpos | hneg
  · left
    rw [coroot_eq_sum_typeDCoroot_smul_simpleCoroot]
    exact sum_zsmul_mem_closure_of_nonneg _ _ hpos
  · right
    rw [coroot_eq_sum_typeDCoroot_smul_simpleCoroot, ← Finset.sum_neg_distrib]
    simp_rw [← neg_smul]
    exact sum_zsmul_mem_closure_of_nonneg _ _ fun i => neg_nonneg.mpr (hneg i)

/-- The Bourbaki-numbered base of the pinned simply connected datum of type `Dₙ`. -/
noncomputable def typeDSimplyConnectedBase (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).Base where
  support := typeDSimpleSupport n hn
  linearIndepOn_root := by
    rw [coe_typeDSimpleSupport hn, linearIndepOn_range_iff (typeDSimpleIndex_injective hn)]
    have hroot : (typeDSimplyConnectedRootDatum n hn).root ∘ typeDSimpleIndex n hn =
        fun i => typeDCharacterRoot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) := rfl
    rw [hroot]
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let v := ∑ i, c i • typeDSimpleRoot n hn i
    have horth : ∀ j, v ⬝ᵥ
          typeDSimpleRoot n hn j = 0 := by
      intro j
      have hj := congrFun hc j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        typeDCharacterRoot, typeDRootEquiv_apply_typeDSimpleIndex] at hj
      change (∑ i, c i • typeDSimpleRoot n hn i) ⬝ᵥ typeDSimpleRoot n hn j = 0
      rw [sum_dotProduct]
      simpa only [smul_dotProduct, smul_eq_mul] using hj
    have hself : v ⬝ᵥ v = 0 := by
      calc
        v ⬝ᵥ v = v ⬝ᵥ ∑ i, c i • typeDSimpleRoot n hn i := rfl
        _ = 0 := by
          rw [dotProduct_sum]
          apply Finset.sum_eq_zero
          intro i _
          rw [dotProduct_smul, horth i, smul_zero]
    have hv : v = 0 := dotProduct_self_eq_zero.mp hself
    exact Fintype.linearIndependent_iff.mp (linearIndependent_typeDSimpleRoot hn) c hv
  linearIndepOn_coroot := by
    rw [coe_typeDSimpleSupport hn, linearIndepOn_range_iff (typeDSimpleIndex_injective hn)]
    have hcoroot : (typeDSimplyConnectedRootDatum n hn).coroot ∘ typeDSimpleIndex n hn =
        fun i => Pi.single i 1 := funext fun i => coroot_typeDSimpleIndex hn i
    rw [hcoroot]
    have hbasis : (fun i : Fin n => Pi.single i (1 : ℤ)) =
        fun i => (Pi.basisFun ℤ (Fin n)) i := by
      funext i j
      simp [Pi.single_apply]
    rw [hbasis]
    exact (Pi.basisFun ℤ (Fin n)).linearIndependent
  root_mem_or_neg_mem k := by
    rw [coe_typeDSimpleSupport, root_typeDSimplyConnectedRootDatum, ← range_comp]
    change typeDCharacterRoot n hn (typeDRootEquiv n hn k) ∈ AddSubmonoid.closure
        (range fun i => typeDCharacterRoot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i))) ∨ _
    exact typeDCharacterRoot_mem_simpleClosure_or_neg hn (typeDRootEquiv n hn k)
  coroot_mem_or_neg_mem k := by
    rw [coe_typeDSimpleSupport, coroot_typeDSimplyConnectedRootDatum, ← range_comp]
    change typeDCoroot n hn (typeDRootEquiv n hn k) ∈ AddSubmonoid.closure
        (range fun i => typeDCoroot n hn
          (typeDRootEquiv n hn (typeDSimpleIndex n hn i))) ∨ _
    exact typeDCoroot_mem_simpleClosure_or_neg hn (typeDRootEquiv n hn k)

/-- Membership in the pinned base support is membership among the first `n` root indices. -/
@[simp] theorem mem_typeDSimplyConnectedBase_support (hn : 4 ≤ n)
    {k : Fin (2 * n * (n - 1))} :
    k ∈ (typeDSimplyConnectedBase n hn).support ↔ (k : ℕ) < n :=
  mem_typeDSimpleSupport hn

private def typeDBaseEquiv (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedBase n hn).support ≃ Fin n where
  toFun x := ⟨(x : Fin (2 * n * (n - 1))), mem_typeDSimpleSupport hn |>.mp x.2⟩
  invFun i := ⟨typeDSimpleIndex n hn i,
    mem_typeDSimpleSupport hn |>.mpr (by simpa only [typeDSimpleIndex_val] using i.isLt)⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    simp only [typeDSimpleIndex_val]
  right_inv i := by
    apply Fin.ext
    simp only [typeDSimpleIndex_val]

private lemma pairing_typeDSimplyConnectedRootDatum (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).pairing k l =
      (typeDSimplyConnectedRootDatum n hn).root k ⬝ᵥ
        (typeDSimplyConnectedRootDatum n hn).coroot l := rfl

private lemma pairing_typeDSimpleIndex (hn : 4 ≤ n) (i j : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).pairing
        (typeDSimpleIndex n hn i) (typeDSimpleIndex n hn j) = CartanMatrix.D n i j := by
  rw [pairing_typeDSimplyConnectedRootDatum, root_typeDSimpleIndex,
    coroot_typeDSimpleIndex, dotProduct_single, mul_one]

/-- The pinned datum and base of type `Dₙ` realize the standard Cartan matrix `CartanMatrix.D n`.
-/
theorem hasCartanType_typeDSimplyConnectedRootDatum (n : ℕ) (hn : 4 ≤ n) :
    HasCartanType (typeDSimplyConnectedRootDatum n hn) (typeDSimplyConnectedBase n hn) (.D n) := by
  rw [hasCartanType_iff]
  refine ⟨typeDBaseEquiv n hn, fun i j => ?_⟩
  have hi : (i : Fin (2 * n * (n - 1))) =
      typeDSimpleIndex n hn (typeDBaseEquiv n hn i) := by
    apply Fin.ext
    simp only [typeDSimpleIndex_val]
    rfl
  have hj : (j : Fin (2 * n * (n - 1))) =
      typeDSimpleIndex n hn (typeDBaseEquiv n hn j) := by
    apply Fin.ext
    simp only [typeDSimpleIndex_val]
    rfl
  rw [← (FaithfulSMul.algebraMap_injective ℤ ℤ).eq_iff,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply, hi, hj]
  rw [pairing_typeDSimpleIndex, cartanMatrix_D]
  rfl

/-- The coroots of the pinned type `Dₙ` datum span the cocharacter lattice. This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. -/
theorem corootSpan_typeDSimplyConnectedRootDatum_eq_top (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).corootSpan ℤ = ⊤ := by
  refine top_unique ?_
  rw [← (Pi.basisFun ℤ (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨typeDSimpleIndex n hn i, by rw [coroot_typeDSimpleIndex]; simp⟩

end DynkinType

end TauCeti
