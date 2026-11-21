import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.PerturbedSpecificationOfAnArrayIsDefined
import YangMills.Construction.InfiniteLattice.SupportsOfAnArrayAreLocallyFinite
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace TiltedKernelConstruction
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
attribute [local instance] secondCountableTopology_specialUnitary
theorem isProbabilityMeasure_haarProd (W : LinkWindow 1) : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd Matrices.ComplexMatrix2.haarPi
  infer_instance
attribute [local instance] isProbabilityMeasure_haarProd
theorem nonempty_gaugeField : Nonempty (GaugeField 1) :=
  ⟨⟨fun _ => 1, fun _ => by simp⟩⟩
theorem finset_sum_mem_continuousLocalFunctions (hLoc : LocalFunctionProperties 1) {ι : Type*}
    (s : Finset ι) (f : ι → GaugeField 1 → ℂ) (hf : ∀ i ∈ s, f i ∈ continuousLocalFunctions 1) :
    (fun U => ∑ i ∈ s, f i U) ∈ continuousLocalFunctions 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hLoc.2.2.1 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hLoc.1 _ (hf i (Finset.mem_insert_self _ _)) _
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))).1
theorem translate_mem (hSym : LatticeSymmetryProperties 1) (A : LocalObservableArray)
    (i : A.Label) : A.translate i ∈ continuousLocalFunctions 1 := by
  have h := (hSym (shift (i.1 : LatticePoint 1)) (shift (i.1 : LatticePoint 1))).2.2.2.2.1
  have hm : A.translate i ∈ (shift (i.1 : LatticePoint 1)).actOn ''
      continuousLocalFunctions 1 := ⟨_, A.gen_mem i.2, rfl⟩
  rwa [h] at hm
theorem ofReal_re_translate (A : LocalObservableArray) (i : A.Label) (U : GaugeField 1) :
    (((A.translate i U).re : ℝ) : ℂ) = A.translate i U := by
  have him : (A.translate i U).im = 0 := A.gen_im i.2 _
  exact Complex.ext (by simp) (by simp [him])
theorem windowEnergy_mem_continuousLocalFunctions (hFace : PlaquetteProperties 1)
    (hLoc : LocalFunctionProperties 1) (hSym : LatticeSymmetryProperties 1)
    (A : LocalObservableArray) (hFin : A.SupportsLocallyFinite) (β t : ℝ) (W : LinkWindow 1) :
    (fun U => (A.windowEnergy β t W U : ℂ)) ∈ continuousLocalFunctions 1 := by
  have hfinFaces := hFace.2.2.2.2.2 W
  have hfinLabels := hFin.finite_labelsTouching W
  have heq : (fun U => (A.windowEnergy β t W U : ℂ)) =
      (β : ℂ) • (fun U : GaugeField 1 => ∑ p ∈ hfinFaces.toFinset, (faceEnergy U p : ℂ)) +
        (-(t : ℂ)) • (fun U => ∑ i ∈ hfinLabels.toFinset, A.translate i U) := by
    funext U
    simp only [LocalObservableArray.windowEnergy, finsum_mem_eq_finite_toFinset_sum _ hfinFaces,
      finsum_mem_eq_finite_toFinset_sum _ hfinLabels, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [ofReal_re_translate]
    ring
  rw [heq]
  refine (hLoc.1 _ (hLoc.2.1 _ _ ?_) _ (hLoc.2.1 _ _ ?_)).1
  · exact finset_sum_mem_continuousLocalFunctions hLoc _ _ fun p _ => (hFace.2.2.2.2.1 p).1
  · exact finset_sum_mem_continuousLocalFunctions hLoc _ _ fun i _ => translate_mem hSym A i
variable (W : LinkWindow 1) (E : GaugeField 1 → ℝ)
def weightedIntegral (F : GaugeField 1 → ℂ) (U : GaugeField 1) : ℂ :=
  ∫ V, F (W.glue one_pos V U) * (Real.exp (-E (W.glue one_pos V U)) : ℂ) ∂W.haarProd
def partitionIntegral (U : GaugeField 1) : ℝ :=
  ∫ V, Real.exp (-E (W.glue one_pos V U)) ∂W.haarProd
variable {W E}
theorem measurable_glue
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (U : GaugeField 1) : Measurable fun V : W.Assignments => W.glue one_pos V U :=
  (hglue.comp (continuous_id.prodMk continuous_const)).measurable
theorem exp_neg_le_exp_bound (C : ℝ) (hC : ∀ U, |E U| ≤ C) (U : GaugeField 1) :
    Real.exp (-E U) ≤ Real.exp C :=
  Real.exp_le_exp.mpr (by linarith [neg_abs_le (E U), hC U])
theorem exp_neg_bound_le (C : ℝ) (hC : ∀ U, |E U| ≤ C) (U : GaugeField 1) :
    Real.exp (-C) ≤ Real.exp (-E U) :=
  Real.exp_le_exp.mpr (by linarith [le_abs_self (E U), hC U])
theorem integrable_boltzmannFactor
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) (U : GaugeField 1) :
    Integrable (fun V : W.Assignments => Real.exp (-E (W.glue one_pos V U))) W.haarProd := by
  refine Integrable.of_bound ?_ (Real.exp C) (Filter.Eventually.of_forall fun V => ?_)
  · exact (Real.measurable_exp.comp
      (hE.measurable.comp (measurable_glue hglue U)).neg).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le_exp_bound C hC _
theorem integrable_weightedIntegrand
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) (U : GaugeField 1) :
    Integrable (fun V : W.Assignments => F (W.glue one_pos V U) *
      (Real.exp (-E (W.glue one_pos V U)) : ℂ)) W.haarProd := by
  obtain ⟨hFm, D, hD⟩ := hF
  refine Integrable.of_bound ?_ (D * Real.exp C) (Filter.Eventually.of_forall fun V => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    exact (hFm.comp (measurable_glue hglue U)).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (hE.measurable.comp (measurable_glue hglue U)).neg))
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (hD _) (exp_neg_le_exp_bound C hC _) (Real.exp_pos _).le
      ((norm_nonneg _).trans (hD U))
theorem exp_neg_le_partitionIntegral
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) (U : GaugeField 1) :
    Real.exp (-C) ≤ partitionIntegral W E U := by
  have h := integral_mono (μ := W.haarProd) (integrable_const (Real.exp (-C)))
    (integrable_boltzmannFactor hglue hE C hC U) (fun V => exp_neg_bound_le C hC _)
  simpa [partitionIntegral] using h
theorem partitionIntegral_pos
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) (U : GaugeField 1) :
    0 < partitionIntegral W E U :=
  (Real.exp_pos _).trans_le (exp_neg_le_partitionIntegral hglue hE C hC U)
theorem norm_le_supNorm {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField 1) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨-, D, hD⟩ := hF
  exact le_ciSup (f := fun U => ‖F U‖) ⟨D, by rintro _ ⟨U, rfl⟩; exact hD U⟩ U
theorem norm_weightedIntegral_le
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) (U : GaugeField 1) :
    ‖weightedIntegral W E F U‖ ≤ observableSupNorm F * partitionIntegral W E U := by
  have hi := integrable_boltzmannFactor hglue hE C hC U
  have h := norm_integral_le_of_norm_le (hi.const_mul (observableSupNorm F))
    (f := fun V : W.Assignments => F (W.glue one_pos V U) *
      (Real.exp (-E (W.glue one_pos V U)) : ℂ))
    (Filter.Eventually.of_forall fun V => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (norm_le_supNorm hF _) (Real.exp_pos _).le)
  rw [integral_const_mul] at h
  exact h
theorem isBoundedObservable_weightedIntegral (hInt : FiniteHaarIntegralsBounded 1)
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (weightedIntegral W E F) := by
  obtain ⟨hFm, D, hD⟩ := hF
  have hw : Continuous fun q : W.Assignments × GaugeField 1 =>
      ((Real.exp (-E (W.glue one_pos q.1 q.2)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hE.comp hglue).neg)
  have hm : @Measurable _ _ (borel (W.Assignments × GaugeField 1)) _
      (fun q : W.Assignments × GaugeField 1 => F (W.glue one_pos q.1 q.2) *
        ((Real.exp (-E (W.glue one_pos q.1 q.2)) : ℝ) : ℂ)) := by
    let _ : MeasurableSpace (W.Assignments × GaugeField 1) := borel _
    have : BorelSpace (W.Assignments × GaugeField 1) := ⟨rfl⟩
    exact (hFm.comp hglue.measurable).mul hw.measurable
  refine (hInt W.links _ hm ⟨D * Real.exp C, fun q => ?_⟩).1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul (hD _) (exp_neg_le_exp_bound C hC _) (Real.exp_pos _).le
    ((norm_nonneg _).trans (hD q.2))
theorem weightedIntegral_one (U : GaugeField 1) :
    weightedIntegral W E (fun _ => 1) U = (partitionIntegral W E U : ℂ) := by
  simp only [weightedIntegral, partitionIntegral, one_mul]
  exact integral_complex_ofReal
theorem isBoundedObservable_one : IsBoundedObservable (fun _ : GaugeField 1 => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem isBoundedObservable_partitionIntegral (hInt : FiniteHaarIntegralsBounded 1)
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) :
    IsBoundedObservable (fun U => (partitionIntegral W E U : ℂ)) := by
  have h := isBoundedObservable_weightedIntegral hInt hglue hE C hC isBoundedObservable_one
  rwa [show weightedIntegral W E (fun _ => 1) = fun U => (partitionIntegral W E U : ℂ) from
    funext weightedIntegral_one] at h
theorem norm_ratio_le
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) (U : GaugeField 1) :
    ‖weightedIntegral W E F U / (partitionIntegral W E U : ℂ)‖ ≤ observableSupNorm F := by
  have hpos := partitionIntegral_pos hglue hE C hC U
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_le_iff₀ hpos]
  exact norm_weightedIntegral_le hglue hE C hC hF U
theorem isBoundedObservable_ratio (hInt : FiniteHaarIntegralsBounded 1)
    (hglue : Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2)
    (hE : Continuous E) (C : ℝ) (hC : ∀ U, |E U| ≤ C) {F : GaugeField 1 → ℂ}
    (hF : IsBoundedObservable F) :
    IsBoundedObservable (fun U => weightedIntegral W E F U / (partitionIntegral W E U : ℂ)) :=
  ⟨(isBoundedObservable_weightedIntegral hInt hglue hE C hC hF).1.div
      (isBoundedObservable_partitionIntegral hInt hglue hE C hC).1,
    observableSupNorm F, norm_ratio_le hglue hE C hC hF⟩
theorem exp_neg_windowEnergy_zero (A : LocalObservableArray) (β : ℝ) (W : LinkWindow 1)
    (U : GaugeField 1) : Real.exp (-A.windowEnergy β 0 W U) = W.localWeight β U := by
  simp [LocalObservableArray.windowEnergy, LinkWindow.localWeight]
theorem tiltedKernel_eq_conditionalExpectation_zero (A : LocalObservableArray) (β : ℝ)
    (W : LinkWindow 1) (F : GaugeField 1 → ℂ) :
    A.tiltedKernel β 0 W F = W.conditionalExpectation one_pos β F := by
  funext U
  simp only [LocalObservableArray.tiltedKernel, LocalObservableArray.windowPartition,
    LinkWindow.conditionalExpectation, exp_neg_windowEnergy_zero]
end TiltedKernelConstruction
open TiltedKernelConstruction in
theorem tiltedKernelOfArrayIsWellDefined
    (hElementary : ElementaryLatticeFacts)
    (hSupports : ArraySupportsLocallyFinite) :
    TiltedKernelOfArrayIsWellDefined := by
  intro β hβ A t
  obtain ⟨hA, hFace, -, hLoc, -, -, -, hSym, hInt⟩ := hElementary 1 β one_pos hβ
  have hFin := hSupports A
  have hglue : ∀ W : LinkWindow 1,
      Continuous fun q : W.Assignments × GaugeField 1 => W.glue one_pos q.1 q.2 := hA.2.2
  have hmem := windowEnergy_mem_continuousLocalFunctions hFace hLoc hSym A hFin β t
  have hcont : ∀ W : LinkWindow 1, Continuous (A.windowEnergy β t W) := fun W => by
    have h := Complex.continuous_re.comp (hmem W).2.2
    simpa [Function.comp_def] using h
  have hbound : ∀ W : LinkWindow 1, ∃ C : ℝ, ∀ U, |A.windowEnergy β t W U| ≤ C := fun W => by
    obtain ⟨C, hC⟩ := (hmem W).1.2
    exact ⟨C, fun U => by simpa [Complex.norm_real] using hC U⟩
  refine ⟨hmem, fun W U => ?_, fun W F hF U => ?_, fun W F hF => ?_, fun W F hF => ?_,
    fun W F _ => tiltedKernel_eq_conditionalExpectation_zero A β W F, ?_⟩
  · obtain ⟨C, hC⟩ := hbound W
    exact partitionIntegral_pos (hglue W) (hcont W) C hC U
  · obtain ⟨C, hC⟩ := hbound W
    exact integrable_weightedIntegrand (hglue W) (hcont W) C hC hF U
  · obtain ⟨C, hC⟩ := hbound W
    exact isBoundedObservable_ratio hInt (hglue W) (hcont W) C hC hF
  · obtain ⟨C, hC⟩ := hbound W
    have := nonempty_gaugeField
    exact ciSup_le (norm_ratio_le (hglue W) (hcont W) C hC hF)
  · ext ν
    simp only [LocalObservableArray.tiltedGibbsClass, gibbsClass, Set.mem_ofPred_eq,
      tiltedKernel_eq_conditionalExpectation_zero]
end YangMills.Construction.InfiniteLattice
