import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import Reconstruction.MinkowskiSpace.ConjugatedInsertionsOfTheKernels
import Reconstruction.MinkowskiSpace.FormWithNoFieldOfAFunctional
import Reconstruction.MinkowskiSpace.InsertionOperatorsOfOneField
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
theorem timeUnitVec_smul_apply (t : ℝ) :
    (t • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx = t := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem realWickPoint_add (a b : Fin 4 → ℝ) :
    realWickPoint (a + b) = realWickPoint a + realWickPoint b := by
  unfold realWickPoint
  rw [← map_add]
  congr 1
  funext μ
  simp [MinkowskiSpace.toComplex]
theorem imagTimeShift_eq_realWickPoint (η : ℝ) :
    FieldForms.imagTimeShift η = realWickPoint (η • FieldFormConditions.timeUnitVec) := by
  have hsucc : ∀ i : Fin 3, MinkowskiSpace.timeUnit i.succ = 0 := fun i => by
    simp [MinkowskiSpace.timeUnit, MinkowskiSpace.mkTimeSpace]
  have hz : MinkowskiSpace.timeUnit 0 = 1 := by
    simp [MinkowskiSpace.timeUnit, MinkowskiSpace.mkTimeSpace]
  have hone : MinkowskiSpace.timeUnit 1 = 0 := hsucc 0
  have htwo : MinkowskiSpace.timeUnit 2 = 0 := hsucc 1
  have hthree : MinkowskiSpace.timeUnit 3 = 0 := hsucc 2
  funext μ
  fin_cases μ <;>
    simp [FieldForms.imagTimeShift, realWickPoint, MinkowskiSpace.wickMap,
      MinkowskiSpace.toComplex, hz, hone, htwo, hthree, FieldFormConditions.timeUnitVec,
      PeriodicLattice.coordVec, TimeAxis.timeIdx]
theorem imInClosedCone_realWickPoint {a : Fin 4 → ℝ} (ha : 0 ≤ a TimeAxis.timeIdx) :
    FieldFormTranslations.ImInClosedCone (realWickPoint a) := by
  have hz : MinkowskiSpace.imPart (realWickPoint a) 0 = a TimeAxis.timeIdx := by
    simp [MinkowskiSpace.imPart, realWickPoint, MinkowskiSpace.wickMap,
      MinkowskiSpace.toComplex, TimeAxis.timeIdx]
  have hspace : MinkowskiSpace.spacePart (MinkowskiSpace.imPart (realWickPoint a)) = 0 := by
    funext i
    fin_cases i <;>
      simp [MinkowskiSpace.spacePart, MinkowskiSpace.imPart, realWickPoint,
        MinkowskiSpace.wickMap, MinkowskiSpace.toComplex]
  show MinkowskiSpace.coneGap (MinkowskiSpace.imPart (realWickPoint a)) ≥ 0
  unfold MinkowskiSpace.coneGap
  rw [hz, hspace]
  simpa [MinkowskiSpace.spaceNorm] using ha
theorem sub_mem_Icc_of_mem_tsupport_translateFun (hker : CubeKernels.KernelFacts) {η : ℝ}
    (hη : 0 < η) (Γ : Finset (Fin 4)) (c : Fin 4 → ℝ) {x : Fin 4 → ℝ}
    (hx : x ∈ tsupport (translateFun c (scaledKernel η Γ))) (μ : Fin 4) :
    x μ - c μ ∈ Icc 0 (η / 8) := by
  have hcube := (hker.2.1.2.2.2.2.2.2 Γ (η / 8) (by positivity)).2
  have hsub : tsupport (scaledKernel η Γ) ⊆ tsupport (CubeKernels.cubeKernel Γ (η / 8)) :=
    tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) _
  have hpre : tsupport (translateFun c (scaledKernel η Γ)) ⊆
      (fun y : Fin 4 → ℝ => y - c) ⁻¹' tsupport (scaledKernel η Γ) :=
    tsupport_comp_subset_preimage (scaledKernel η Γ) (continuous_id.sub continuous_const)
  exact hcube (hsub (hpre hx)) μ
theorem isAdmissible_translateFun_scaledKernel (hker : CubeKernels.KernelFacts) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (Γ : Finset (Fin 4)) {c : Fin 4 → ℝ}
    (hc : η ≤ c TimeAxis.timeIdx) (hc' : c TimeAxis.timeIdx + η / 8 ≤ 3 * η) :
    IsAdmissible η (translateFun c (scaledKernel η Γ)) := by
  have hk := (hker.2.1.2.2.2.2.2.2 Γ (η / 8) (by positivity)).1
  have hdiff : ContDiff ℝ 1 (scaledKernel η Γ) :=
    Complex.ofRealCLM.contDiff.comp hk.1
  have hcpt : HasCompactSupport (scaledKernel η Γ) :=
    HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hk.2 (by simp)
  refine ⟨⟨hdiff.comp (contDiff_id.sub contDiff_const), ?_, subset_univ _⟩, fun x hx => ?_,
    fun x hx y hy => ?_⟩
  · exact hcpt.comp_homeomorph (Homeomorph.subRight c)
  · have h := sub_mem_Icc_of_mem_tsupport_translateFun hker hη Γ c hx TimeAxis.timeIdx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · have hd : ∀ μ, (x - y) μ ^ 2 ≤ (1 / 8) ^ 2 := fun μ => by
      have hxμ := sub_mem_Icc_of_mem_tsupport_translateFun hker hη Γ c hx μ
      have hyμ := sub_mem_Icc_of_mem_tsupport_translateFun hker hη Γ c hy μ
      rw [Pi.sub_apply]
      exact sq_le_sq' (by linarith [hxμ.1, hxμ.2, hyμ.1, hyμ.2])
        (by linarith [hxμ.1, hxμ.2, hyμ.1, hyμ.2])
    refine Real.sqrt_le_iff.mpr ⟨zero_le_one, ?_⟩
    rw [Fin.sum_univ_four]
    linarith [hd 0, hd 1, hd 2, hd 3]
theorem translateFun_translateFun (a b : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) :
    translateFun a (translateFun b f) = translateFun (b + a) f := by
  funext x
  simp only [translateFun]
  congr 1
  abel
theorem kernelInsertionConjugation_holds (hins : InsertionOperators.InsertionOperatorBounds)
    (hzero : ZeroFieldForm)
    (htrans : FieldFormTranslations.TranslationOperatorFacts)
    (hker : CubeKernels.KernelFacts) : KernelInsertionConjugation := by
  intro sigma E p C H η Γ a hη hη1 ha
  obtain ⟨halo, hahi⟩ := abs_le.mp ha
  have hbase : IsAdmissible η
      (translateFun ((2 * η) • FieldFormConditions.timeUnitVec) (scaledKernel η Γ)) :=
    isAdmissible_translateFun_scaledKernel hker hη hη1 Γ
      (by rw [timeUnitVec_smul_apply]; linarith)
      (by rw [timeUnitVec_smul_apply]; linarith)
  have hmoved : IsAdmissible η
      (translateFun ((2 * η) • FieldFormConditions.timeUnitVec + a) (scaledKernel η Γ)) :=
    isAdmissible_translateFun_scaledKernel hker hη hη1 Γ
      (by rw [Pi.add_apply, timeUnitVec_smul_apply]; linarith)
      (by rw [Pi.add_apply, timeUnitVec_smul_apply]; linarith)
  refine ⟨hmoved, ?_⟩
  have hcov := (hins sigma E p C H η hη hη1).2.2
  have hmul : ∀ b c : Fin 4 → ℝ, 0 ≤ b TimeAxis.timeIdx → 0 ≤ c TimeAxis.timeIdx →
      FieldForms.spectralTranslation E (realWickPoint b) *
          FieldForms.spectralTranslation E (realWickPoint c) =
        FieldForms.spectralTranslation E (realWickPoint (b + c)) := fun b c hb hc => by
    rw [realWickPoint_add]
    exact ((htrans _ E (FieldFormConditions.vacuumState sigma) (fun _ => 0) 0 1
      (hzero sigma E p C H)).1.1 _ _
      (imInClosedCone_realWickPoint hb) (imInClosedCone_realWickPoint hc)).2.1
  have htime : (η • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx = η :=
    timeUnitVec_smul_apply η
  rw [imagTimeShift_eq_realWickPoint]
  unfold conjKernelInsertion kernelInsertion
  by_cases hnn : 0 ≤ a TimeAxis.timeIdx
  · have hc := hcov _ a hbase hnn
      (by rw [translateFun_translateFun]; exact hmoved)
    rw [translateFun_translateFun] at hc
    have hleft := hmul a (η • FieldFormConditions.timeUnitVec - a) hnn
      (by rw [Pi.sub_apply, htime]; linarith)
    rw [add_sub_cancel] at hleft
    have hright := hmul (η • FieldFormConditions.timeUnitVec) a (by rw [htime]; exact hη.le) hnn
    calc _ = FieldForms.spectralTranslation E (realWickPoint (η • FieldFormConditions.timeUnitVec)) *
            (insertionOp sigma η
              (translateFun ((2 * η) • FieldFormConditions.timeUnitVec + a) (scaledKernel η Γ)) *
              FieldForms.spectralTranslation E (realWickPoint a)) *
            FieldForms.spectralTranslation E
              (realWickPoint (η • FieldFormConditions.timeUnitVec - a)) := by
          rw [← hleft]; simp only [mul_assoc]
      _ = _ := by rw [hc, ← hright]; simp only [mul_assoc]
  · have hneg : 0 ≤ (-a) TimeAxis.timeIdx := by
      rw [Pi.neg_apply]
      linarith
    have hback : translateFun (-a)
        (translateFun ((2 * η) • FieldFormConditions.timeUnitVec + a) (scaledKernel η Γ)) =
        translateFun ((2 * η) • FieldFormConditions.timeUnitVec) (scaledKernel η Γ) := by
      rw [translateFun_translateFun, add_neg_cancel_right]
    have hc := hcov _ (-a) hmoved hneg (by rw [hback]; exact hbase)
    rw [hback] at hc
    have hleft := hmul (η • FieldFormConditions.timeUnitVec + a) (-a)
      (by rw [Pi.add_apply, htime]; linarith) hneg
    rw [add_neg_cancel_right] at hleft
    have hright := hmul (-a) (η • FieldFormConditions.timeUnitVec) hneg (by rw [htime]; exact hη.le)
    rw [neg_add_eq_sub] at hright
    calc _ = FieldForms.spectralTranslation E
              (realWickPoint (η • FieldFormConditions.timeUnitVec + a)) *
            (FieldForms.spectralTranslation E (realWickPoint (-a)) *
              insertionOp sigma η
                (translateFun ((2 * η) • FieldFormConditions.timeUnitVec + a) (scaledKernel η Γ))) *
            FieldForms.spectralTranslation E (realWickPoint (η • FieldFormConditions.timeUnitVec)) := by
          rw [← hleft]; simp only [mul_assoc]
      _ = _ := by rw [← hc, ← hright]; simp only [mul_assoc]
end YangMills.Construction.InsertedFieldForm
end
