/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMeasure.LaplaceFunctional
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.ProductKernel
import Mathlib.Probability.Independence.Integration

/-!
# Independently marking finitely many occurrences

`Kernel.finiteMarking K` attaches independent marks of law `K (x i)` to a finite family
of ground locations `x`. Its output is a measure, not a set: repeated ground locations
are marked separately, and coincident marked locations retain their multiplicities.

The ground projection recovers the original sum of Dirac occurrences. Reindexing the
occurrences leaves the marked law unchanged. The integration and Laplace formulas describe
the law without exposing the product-space realization. These are the finite-window
ingredients for independent marking and thinning of point measures.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5, on independent marking.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {X E ι : Type*} [MeasurableSpace X] [MeasurableSpace E] [Fintype ι]

/-- The law of independently marking the occurrences `x i`, with mark law `K (x i)`.
Each index contributes one occurrence, including when different indices have the same location. -/
def finiteMarking (K : Kernel X E) [IsMarkovKernel K] :
    Kernel (ι → X) (Measure (X × E)) where
  toFun x := (Measure.pi fun i => K (x i)).map fun z => ∑ i, Measure.dirac (x i, z i)
  measurable' := by
    have hp : Measurable fun x : ι → X =>
        ProbabilityMeasure.pi fun i => (⟨K (x i), inferInstance⟩ : ProbabilityMeasure E) :=
      TauCeti.MeasureTheory.measurable_probabilityMeasure_pi.comp
        (Measurable.of_eval fun i =>
          (K.measurable.comp (measurable_pi_apply i)).subtype_mk)
    have hs : Measurable (Function.uncurry fun (x : ι → X) (z : ι → E) =>
        ∑ i, Measure.dirac (x i, z i)) := by
      exact Finset.measurable_sum _ fun i _ => Measure.measurable_dirac.comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))
    exact measurable_subtype_coe.comp
      ((TauCeti.MeasureTheory.measurable_probabilityMeasure_map_of_measurable_uncurry hs).comp
        (hp.prodMk measurable_id))

/-- Evaluation of the finite marking kernel as a product-space pushforward. -/
theorem finiteMarking_apply (K : Kernel X E) [IsMarkovKernel K] (x : ι → X) :
    K.finiteMarking x =
      (Measure.pi fun i => K (x i)).map (fun z => ∑ i, Measure.dirac (x i, z i)) := (rfl)

instance (K : Kernel X E) [IsMarkovKernel K] : IsMarkovKernel (K.finiteMarking (ι := ι)) :=
  ⟨fun x => by
    rw [finiteMarking_apply]
    exact (Measure.isProbabilityMeasure_map_iff (by
      fun_prop : Measurable (fun z : ι → E => ∑ i, Measure.dirac (x i, z i))).aemeasurable).2
        inferInstance⟩

variable (K : Kernel X E) [IsMarkovKernel K]

/-- Integrate a test of the marked configuration by independently integrating its marks. -/
theorem lintegral_finiteMarking (x : ι → X) {g : Measure (X × E) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂K.finiteMarking x =
      ∫⁻ z, g (∑ i, Measure.dirac (x i, z i)) ∂Measure.pi (fun i => K (x i)) := by
  rw [finiteMarking_apply, MeasureTheory.lintegral_map hg (by fun_prop)]

/-- Independent marking preserves the ground configuration, including multiplicities. -/
@[simp] theorem finiteMarking_map_fst (x : ι → X) :
    (K.finiteMarking x).map (fun ξ => ξ.map Prod.fst) =
      Measure.dirac (∑ i, Measure.dirac (x i)) := by
  rw [finiteMarking_apply, Measure.map_map (Measure.measurable_map _ measurable_fst)
    (by fun_prop : Measurable (fun z : ι → E => ∑ i, Measure.dirac (x i, z i)))]
  simp only [Function.comp_def, Measure.map_finset_sum' measurable_fst.aemeasurable,
    Measure.map_dirac' measurable_fst]
  simp

/-- Reindexing occurrences does not affect the marked law. In particular, no ordering of
repeated ground locations is distinguished. -/
theorem finiteMarking_comp_equiv {ι' : Type*} [Fintype ι'] (e : ι' ≃ ι) (x : ι → X) :
    K.finiteMarking (x ∘ e) = K.finiteMarking x := by
  let r : (ι' → E) ≃ᵐ (ι → E) := MeasurableEquiv.piCongrLeft (fun _ : ι => E) e
  have hr : (Measure.pi fun i => K (x (e i))).map r = Measure.pi (fun i => K (x i)) :=
    (measurePreserving_piCongrLeft (fun i => K (x i)) e).map_eq
  rw [finiteMarking_apply, finiteMarking_apply, ← hr,
    Measure.map_map (by fun_prop :
      Measurable (fun z : ι → E => ∑ i, Measure.dirac (x i, z i))) r.measurable]
  congr 1
  funext z
  calc
    (∑ i, Measure.dirac ((x ∘ e) i, z i)) =
        ∑ i, Measure.dirac (x (e i), r z (e i)) := by
      simp [r, MeasurableEquiv.piCongrLeft_apply_apply]
    _ = _ := e.sum_comp (fun i => Measure.dirac (x i, r z i))

/-- With no ground occurrences, the marking law is concentrated on the zero measure. -/
@[simp] theorem finiteMarking_of_isEmpty [IsEmpty ι] (x : ι → X) :
    K.finiteMarking x = Measure.dirac 0 := by
  rw [finiteMarking_apply]
  simp

/-- A single ground occurrence receives a single mark with the prescribed law. -/
@[simp] theorem finiteMarking_of_unique [Unique ι] (x : ι → X) :
    K.finiteMarking x = (K (x default)).map (fun z => Measure.dirac (x default, z)) := by
  rw [finiteMarking_apply, ← (measurePreserving_piUnique (fun i => K (x i))).symm.map_eq,
    Measure.map_map (by fun_prop :
      Measurable (fun z : ι → E => ∑ i, Measure.dirac (x i, z i)))
      (MeasurableEquiv.piUnique (fun _ : ι => E)).symm.measurable]
  congr 1
  funext z
  simp

/-- The mean marked measure is the sum of the individual location-tagged mark laws. -/
theorem bind_finiteMarking (x : ι → X) :
    (K.finiteMarking x).bind id = ∑ i, (K (x i)).map (Prod.mk (x i)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind measurable_id.aemeasurable hf.aemeasurable]
  simp only [id_eq]
  rw [lintegral_finiteMarking K x (Measure.measurable_lintegral hf)]
  simp only [lintegral_finsetSum_measure, lintegral_dirac' _ hf]
  rw [lintegral_finsetSum Finset.univ (f := fun i (z : ι → E) => f (x i, z i))
    (fun _ _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.lintegral_map hf measurable_prodMk_left]
  exact (measurePreserving_eval (fun i => K (x i)) i).lintegral_comp
    (f := fun z : E => f (x i, z)) (hf.comp measurable_prodMk_left)

/-- The Laplace functional of independent marks is a product of one-occurrence transforms.
Tests may be infinite, and neither simplicity nor distinct ground locations are required. -/
theorem laplaceFunctional_finiteMarking (x : ι → X) {f : X × E → ℝ≥0∞}
    (hf : Measurable f) :
    (K.finiteMarking x).laplaceFunctional id f =
      ∏ i, ∫⁻ z, (ENNReal.expNeg (f (x i, z)) : ℝ≥0∞) ∂K (x i) := by
  rw [Measure.laplaceFunctional_def,
    lintegral_finiteMarking K x (Measure.measurable_expNeg_lintegral measurable_id hf)]
  simp only [id_eq, lintegral_finsetSum_measure, lintegral_dirac' _ hf,
    ENNReal.expNeg_sum, ENNReal.ofNNReal_finsetProd]
  have hi : ProbabilityTheory.iIndepFun (fun i (z : ι → E) =>
      (ENNReal.expNeg (f (x i, z i)) : ℝ≥0∞)) (Measure.pi fun i => K (x i)) :=
    iIndepFun_pi (fun i => (measurable_coe_nnreal_ennreal.comp
      (ENNReal.measurable_expNeg.comp (hf.comp measurable_prodMk_left))).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hi (fun i => by fun_prop)]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval (fun i => K (x i)) i).lintegral_comp
    (f := fun z : E => (ENNReal.expNeg (f (x i, z)) : ℝ≥0∞)) (by fun_prop)

end ProbabilityTheory.Kernel
