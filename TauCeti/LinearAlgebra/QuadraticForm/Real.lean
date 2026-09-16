/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import TauCeti.Data.SignType.Cardinality
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Classification of real quadratic forms by their signature

Mathlib proves the two halves of Sylvester's law of inertia separately: every real quadratic form
on a finite-dimensional space is equivalent to a weighted sum of squares with weights `1`, `0`
and `-1`, and the numbers of positive and of negative weights are the invariants `sigPos` and
`sigNeg`.  This file combines them into the classification itself: two real quadratic forms are
isometric exactly when their dimensions and their two indices of inertia agree.  For a
nondegenerate form the two indices already determine the dimension, so a regular real form is
classified by its signature alone.

The file also supplies the normal form realizing a prescribed signature, the orthogonal sum of
`p` copies of `⟨1⟩` and `q` copies of `⟨-1⟩`, and shows that every regular real form is isometric
to the normal form of its own signature.

## Main results

* `QuadraticForm.sigPos_weightedSumSquares_signType` and
  `QuadraticForm.sigNeg_weightedSumSquares_signType`: the two indices of inertia of a
  sign-weighted sum of squares count the weights `1` and the weights `-1`.
* `QuadraticForm.equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq`: two real quadratic forms
  on finite-dimensional spaces are isometric exactly when their dimensions and both indices of
  inertia agree.
* `QuadraticForm.equivalent_iff_sigPos_eq_and_sigNeg_eq`: two nondegenerate real quadratic forms
  are isometric exactly when their signatures agree.
* `QuadraticForm.realSignatureForm`: the normal form of signature `(p, q)`.
* `QuadraticForm.sigPos_realSignatureForm`, `QuadraticForm.sigNeg_realSignatureForm` and
  `QuadraticForm.nondegenerate_realSignatureForm`: every signature is realized by a regular form.
* `QuadraticForm.equivalent_realSignatureForm`: a regular real quadratic form is isometric to the
  normal form of its signature.
* `QuadraticForm.equivalent_realSignatureForm_iff`: distinct signatures give non-isometric normal
  forms.
* `QuadraticForm.discr_formClass_eq_sigNeg_nsmul`: the discriminant square class of a regular
  real form is the parity of its negative index.
* `QuadraticForm.sign_discr`: the sign of the Gram determinant is `(-1) ^ sigNeg Q`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section
noncomputable section

open Finset QuadraticMap

namespace QuadraticForm

section Fibers

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The positive index of inertia of a sign-weighted sum of squares counts the weights `1`. -/
theorem sigPos_weightedSumSquares_signType (u : ι → SignType) :
    sigPos (weightedSumSquares ℝ fun i ↦ ((u i : ℝ))) = {i | u i = 1}.ncard := by
  rw [sigPos_weightedSumSquares]
  congr 1
  ext i
  cases h : u i <;> simp [h]

/-- The negative index of inertia of a sign-weighted sum of squares counts the weights `-1`. -/
theorem sigNeg_weightedSumSquares_signType (u : ι → SignType) :
    sigNeg (weightedSumSquares ℝ fun i ↦ ((u i : ℝ))) = {i | u i = -1}.ncard := by
  rw [sigNeg_weightedSumSquares]
  congr 1
  ext i
  cases h : u i <;> simp [h]

/-- Two sign-weighted sums of squares are isometric as soon as each of the three weights occurs
the same number of times in both. -/
private theorem equivalent_weightedSumSquares_of_ncard_fiber_eq (u : ι → SignType)
    (u' : ι' → SignType) (h : ∀ s : SignType, {i | u i = s}.ncard = {i' | u' i' = s}.ncard) :
    Equivalent (weightedSumSquares ℝ fun i ↦ ((u i : ℝ)))
      (weightedSumSquares ℝ fun i' ↦ ((u' i' : ℝ))) := by
  have hfiber : ∀ s : SignType, {i // u i = s} ≃ {i' // u' i' = s} := fun s ↦ by
    refine (Fintype.card_eq.mp ?_).some
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact h s
  let σ : ι ≃ ι' := Equiv.ofFiberEquiv hfiber
  have hσ : ∀ i, u' (σ i) = u i := fun i ↦ Equiv.ofFiberEquiv_map hfiber i
  have hcomp : (fun i' ↦ ((u' i' : ℝ))) ∘ σ = fun i ↦ ((u i : ℝ)) := by
    funext i
    exact congrArg (fun s : SignType ↦ ((s : ℝ))) (hσ i)
  exact ⟨((isometryEquivWeightedSumSquaresReindex (R := ℝ) (fun i' ↦ ((u' i' : ℝ))) σ).trans
    (weightedSumSquaresCongr hcomp)).symm⟩

end Fibers

variable {M M' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup M'] [Module ℝ M']
  [FiniteDimensional ℝ M] [FiniteDimensional ℝ M']

/-- **Sylvester's law of inertia**, classification form: two real quadratic forms on
finite-dimensional spaces are isometric exactly when their dimensions agree and both indices of
inertia agree.  The dimension is a genuine third condition: it records the number of zero weights
in a diagonalization, which the two indices do not see. -/
theorem equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq (Q : _root_.QuadraticForm ℝ M)
    (Q' : _root_.QuadraticForm ℝ M') :
    Q.Equivalent Q' ↔ Module.finrank ℝ M = Module.finrank ℝ M' ∧
      sigPos Q = sigPos Q' ∧ sigNeg Q = sigNeg Q' := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv.finrank_eq, Equivalent.sigPos_eq ⟨e⟩, Equivalent.sigNeg_eq ⟨e⟩⟩
  · rintro ⟨hrank, hpos, hneg⟩
    obtain ⟨u, hu⟩ := Q.equivalent_signType_weighted_sum_squared
    obtain ⟨u', hu'⟩ := Q'.equivalent_signType_weighted_sum_squared
    refine hu.trans ((equivalent_weightedSumSquares_of_ncard_fiber_eq u u' ?_).trans hu'.symm)
    have hposFiber : {i | u i = 1}.ncard = {i' | u' i' = 1}.ncard := by
      rw [← sigPos_weightedSumSquares_signType, ← sigPos_weightedSumSquares_signType,
        ← hu.sigPos_eq, ← hu'.sigPos_eq, hpos]
    have hnegFiber : {i | u i = -1}.ncard = {i' | u' i' = -1}.ncard := by
      rw [← sigNeg_weightedSumSquares_signType, ← sigNeg_weightedSumSquares_signType,
        ← hu.sigNeg_eq, ← hu'.sigNeg_eq, hneg]
    have hsum := SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos u
    have hsum' := SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos u'
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum hsum'
    have hzeroFiber : {i | u i = 0}.ncard = {i' | u' i' = 0}.ncard := by omega
    intro s
    cases s
    · exact hzeroFiber
    · exact hnegFiber
    · exact hposFiber

/-- **Sylvester's law of inertia** for regular forms: two nondegenerate real quadratic forms are
isometric exactly when their signatures agree. -/
theorem equivalent_iff_sigPos_eq_and_sigNeg_eq {Q : _root_.QuadraticForm ℝ M}
    {Q' : _root_.QuadraticForm ℝ M'} (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) :
    Q.Equivalent Q' ↔ sigPos Q = sigPos Q' ∧ sigNeg Q = sigNeg Q' := by
  rw [equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq]
  refine ⟨fun h ↦ ⟨h.2.1, h.2.2⟩, fun h ↦ ⟨?_, h.1, h.2⟩⟩
  rw [← sigPos_add_sigNeg_of_nondegenerate Q hQ, ← sigPos_add_sigNeg_of_nondegenerate Q' hQ',
    h.1, h.2]

/-! ### The determinant sign -/

/-- The discriminant square class of a regular real quadratic form is the class of `-1` repeated
its negative index of inertia times. This is the basis-free form of the determinant-sign formula.
-/
theorem discr_formClass_eq_sigNeg_nsmul (Q : _root_.QuadraticForm ℝ M)
    (hQ : Q.Nondegenerate) :
    TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ) =
      sigNeg Q • TauCeti.squareClass (-1 : ℝˣ) := by
  classical
  obtain ⟨w, hw, hQw⟩ := Q.equivalent_one_neg_one_weighted_sum_squared
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  let u : Fin (Module.finrank ℝ M) → ℝˣ := fun i ↦ Units.mk0 (w i) (by
    rcases hw i with hi | hi <;> simp [hi])
  have hQu : Q.Equivalent (QuadraticMap.weightedSumSquares ℝ fun i ↦ (u i : ℝ)) := by
    simpa only [u, Units.val_mk0] using hQw
  rw [TauCeti.discr_formClass Q hQ ⟨Module.finrank ℝ M, u⟩ (by
    rw [TauCeti.presentedForm_eq_weightedSumSquares]
    exact hQu)]
  have hprod := TauCeti.squareClass_prod (Finset.univ : Finset (Fin (Module.finrank ℝ M))) u
  rw [show TauCeti.squareClass (∏ i, u i) = ∑ i, TauCeti.squareClass (u i) by
    simpa using hprod]
  have hu (i : Fin (Module.finrank ℝ M)) :
      TauCeti.squareClass (u i) =
        if w i < 0 then TauCeti.squareClass (-1 : ℝˣ) else 0 := by
    rcases hw i with hi | hi
    · have hui : u i = (-1 : ℝˣ) := by
        ext
        simp [u, hi]
      rw [hui, ite_eq_left (by rw [hi]; norm_num)]
    · have hui : u i = (1 : ℝˣ) := by
        ext
        simp [u, hi]
      rw [hui, ite_eq_right (by rw [hi]; norm_num)]
      exact (TauCeti.squareClass_eq_zero_iff 1).mpr ⟨1, by simp⟩
  simp_rw [hu]
  change (∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ M))),
      if w i < 0 then TauCeti.squareClass (-1 : ℝˣ) else 0) = _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  rw [Q.sigNeg_of_equiv_weightedSumSquares hQw]
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext i
  simp

/-- The sign of the Gram determinant of a regular real quadratic form is `-1` to the power of
its negative index of inertia. The statement is independent of the basis, as its right-hand side
shows. -/
theorem sign_discr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : _root_.QuadraticForm ℝ M)
    (hQ : Q.Nondegenerate) (b : Module.Basis ι ℝ M) :
    SignType.sign (Q.discr b) = (-1 : SignType) ^ sigNeg Q := by
  classical
  -- Reindex a Sylvester normal form by the given basis, so both discriminants use `ι`.
  obtain ⟨w, hw, hQw⟩ := Q.equivalent_one_neg_one_weighted_sum_squared
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  have hcard : Fintype.card ι = Fintype.card (Fin (Module.finrank ℝ M)) := by
    rw [Fintype.card_fin]
    exact (Module.finrank_eq_card_basis b).symm
  let σ : ι ≃ Fin (Module.finrank ℝ M) := Fintype.equivOfCardEq hcard
  let v : ι → ℝ := w ∘ σ
  have hv (i : ι) : v i = -1 ∨ v i = 1 := hw (σ i)
  have hQv : Q.Equivalent (QuadraticMap.weightedSumSquares ℝ v) :=
    hQw.trans (TauCeti.equivalent_weightedSumSquares_comp w σ)
  have hneg : sigNeg Q = {i | v i < 0}.ncard :=
    Q.sigNeg_of_equiv_weightedSumSquares hQv
  obtain ⟨e⟩ := hQv
  have hcomp : Q = (QuadraticMap.weightedSumSquares ℝ v).comp e.toLinearEquiv.toLinearMap := by
    ext x
    exact (e.map_app' x).symm
  -- Changing basis multiplies the diagonal determinant by a nonzero square.
  conv_lhs =>
    rw [hcomp, QuadraticForm.discr_comp (Pi.basisFun ℝ ι)
      (QuadraticMap.weightedSumSquares ℝ v) e.toLinearEquiv.toLinearMap,
      QuadraticForm.discr_eq_discr', QuadraticForm.discr'_weightedSumSquares,
      sign_mul, sign_mul]
  let A := LinearMap.toMatrix b (Pi.basisFun ℝ ι) e.toLinearEquiv.toLinearMap
  have hdet : A.det ≠ 0 := by
    exact (LinearEquiv.isUnit_det e.toLinearEquiv b (Pi.basisFun ℝ ι)).ne_zero
  have hsignA : SignType.sign A.det * SignType.sign A.det = 1 := by
    have hs : SignType.sign A.det ≠ 0 := sign_ne_zero.mpr hdet
    cases h : SignType.sign A.det <;> simp_all
  rw [hsignA, one_mul]
  -- The remaining diagonal product has one negative factor for each negative square.
  -- Expose the bundled sign homomorphism so its finite-product law rewrites.
  change (signHom : ℝ →*₀ SignType) (∏ i, v i) = _
  rw [map_prod]
  change (∏ i, SignType.sign (v i)) = _
  have hsign (i : ι) : SignType.sign (v i) = if v i < 0 then -1 else 1 := by
    rcases hv i with hi | hi
    · rw [hi, ite_eq_left (by norm_num)]
      norm_num
    · rw [hi, ite_eq_right (by norm_num)]
      norm_num
  simp_rw [hsign]
  -- Expose the `Fintype` product as the `univ` product used by `Finset.prod_ite`.
  change (∏ i ∈ (Finset.univ : Finset ι), if v i < 0 then (-1 : SignType) else 1) = _
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
  congr 1
  rw [hneg, Set.ncard_eq_toFinset_card]
  congr 1
  ext i
  simp

/-- The normal form of signature `(p, q)`: the orthogonal sum of `p` copies of `⟨1⟩` and `q`
copies of `⟨-1⟩`. -/
def realSignatureForm (p q : ℕ) : _root_.QuadraticForm ℝ (Fin p ⊕ Fin q → ℝ) :=
  weightedSumSquares ℝ (Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1)

@[simp]
theorem realSignatureForm_apply (p q : ℕ) (x : Fin p ⊕ Fin q → ℝ) :
    realSignatureForm p q x =
      (∑ i : Fin p, x (Sum.inl i) ^ 2) - ∑ j : Fin q, x (Sum.inr j) ^ 2 := by
  simp [realSignatureForm, weightedSumSquares_apply, Fintype.sum_sum_type, _root_.sq,
    sub_eq_add_neg]

/-- The positive index of inertia of the normal form `realSignatureForm p q` is `p`. -/
@[simp]
theorem sigPos_realSignatureForm (p q : ℕ) : sigPos (realSignatureForm p q) = p := by
  have hset : {x : Fin p ⊕ Fin q | 0 < Sum.elim (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) x} =
      Sum.inl '' Set.univ := by
    ext x
    cases x <;> simp
  rw [realSignatureForm, sigPos_weightedSumSquares, hset,
    Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The negative index of inertia of the normal form `realSignatureForm p q` is `q`. -/
@[simp]
theorem sigNeg_realSignatureForm (p q : ℕ) : sigNeg (realSignatureForm p q) = q := by
  have hset : {x : Fin p ⊕ Fin q | Sum.elim (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) x < 0} =
      Sum.inr '' Set.univ := by
    ext x
    cases x <;> simp
  rw [realSignatureForm, sigNeg_weightedSumSquares, hset,
    Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The normal form of signature `(p, q)` is regular, so every signature is realized by a regular
real quadratic form. -/
@[simp]
theorem nondegenerate_realSignatureForm (p q : ℕ) : (realSignatureForm p q).Nondegenerate := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero]
  have hsum := sigPos_add_sigNeg_add_radical (Q := realSignatureForm p q)
  rw [sigPos_realSignatureForm, sigNeg_realSignatureForm] at hsum
  have hdim : Module.finrank ℝ (Fin p ⊕ Fin q → ℝ) = p + q := by simp
  omega

/-- Two normal forms are isometric exactly when their signatures coincide, so the signature is a
complete and independent system of invariants for regular real quadratic forms. -/
@[simp]
theorem equivalent_realSignatureForm_iff (p q p' q' : ℕ) :
    (realSignatureForm p q).Equivalent (realSignatureForm p' q') ↔ p = p' ∧ q = q' := by
  rw [equivalent_iff_sigPos_eq_and_sigNeg_eq (nondegenerate_realSignatureForm p q)
    (nondegenerate_realSignatureForm p' q')]
  simp

/-- Every regular real quadratic form is isometric to the normal form of its signature. -/
theorem equivalent_realSignatureForm (Q : _root_.QuadraticForm ℝ M) (hQ : Q.Nondegenerate) :
    Q.Equivalent (realSignatureForm (sigPos Q) (sigNeg Q)) :=
  (equivalent_iff_sigPos_eq_and_sigNeg_eq hQ (nondegenerate_realSignatureForm _ _)).mpr
    ⟨(sigPos_realSignatureForm _ _).symm, (sigNeg_realSignatureForm _ _).symm⟩

end QuadraticForm
