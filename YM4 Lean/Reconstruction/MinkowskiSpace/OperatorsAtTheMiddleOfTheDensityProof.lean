import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import Reconstruction.MinkowskiSpace.ConjugatedInsertionsOfTheKernelsProof
import Reconstruction.MinkowskiSpace.DensityNearTheMiddleOfASlabProof
import Reconstruction.MinkowskiSpace.OperatorsAtTheMiddleOfTheDensity
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.MidpointOperators
theorem timeComponent_smul_timeUnitVec (t : ℝ) :
    (t • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx = t := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem realWickPoint_add (x y : Fin 4 → ℝ) :
    InsertedFieldForm.realWickPoint (x + y) =
      InsertedFieldForm.realWickPoint x + InsertedFieldForm.realWickPoint y := by apply _root_.YangMills.Construction.InsertedFieldForm.realWickPoint_add <;> assumption
theorem realWickPoint_smul_timeUnitVec (t : ℝ) :
    InsertedFieldForm.realWickPoint (t • FieldFormConditions.timeUnitVec) =
      FieldForms.imagTimeShift t := by apply _root_.YangMills.Construction.CentralDensity.realWickPoint_smul_timeUnitVec <;> assumption
theorem imInClosedCone_realWickPoint {x : Fin 4 → ℝ} (hx : 0 ≤ x TimeAxis.timeIdx) :
    FieldFormTranslations.ImInClosedCone (InsertedFieldForm.realWickPoint x) := by apply _root_.YangMills.Construction.InsertedFieldForm.imInClosedCone_realWickPoint <;> assumption
theorem div_three_rpow {m : ℝ} (hm : 0 < m) (p : ℝ) :
    (m / 3) ^ (-p - 5) = (3 : ℝ) ^ (p + 5) * m ^ (-(p + 5)) := by
  have hexp : -p - 5 = -(p + 5) := by ring
  rw [hexp, Real.div_rpow hm.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp
theorem midpointOperatorFacts_holds
    (hTrans : FieldFormTranslations.TranslationOperatorFacts)
    (hZero : InsertedFieldForm.ZeroFieldForm)
    (hKernel : SmoothedKernelField.Regularity) : MidpointOperatorFacts := by
  intro σ E p C hcond G hG
  have hT := (hTrans (FieldFormConditions.StateSpace σ) E (FieldFormConditions.vacuumState σ)
    (fun _ => 0) 0 1 (hZero σ E p C hcond)).1.1
  have hmul : ∀ x x' : Fin 4 → ℝ, 0 ≤ x TimeAxis.timeIdx → 0 ≤ x' TimeAxis.timeIdx →
      FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint x) *
          FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint x') =
        FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint (x + x')) := by
    intro x x' hx hx'
    rw [realWickPoint_add]
    exact (hT _ _ (imInClosedCone_realWickPoint hx) (imInClosedCone_realWickPoint hx')).2.1
  have hcontr : ∀ x : Fin 4 → ℝ, 0 ≤ x TimeAxis.timeIdx →
      ‖FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint x)‖ ≤ 1 := fun x hx =>
    (hT _ _ (imInClosedCone_realWickPoint hx) (imInClosedCone_realWickPoint hx)).1
  have hmid : ∀ s η : ℝ, 0 < η → η ≤ 1 → 3 * η ≤ s →
      InsertedFieldForm.midpointField σ G s =
        FieldForms.spectralTranslation E
            (InsertedFieldForm.realWickPoint ((s - 3 * η) • FieldFormConditions.timeUnitVec)) *
          InsertedFieldForm.smoothedFieldOp σ E η 0 *
            FieldForms.spectralTranslation E
              (InsertedFieldForm.realWickPoint ((s - 3 * η) • FieldFormConditions.timeUnitVec)) := by
    intro s η hη hη1 hs
    have hform := hG.eq_conj (2 * s) η (s • FieldFormConditions.timeUnitVec) hη hη1
      (by rw [timeComponent_smul_timeUnitVec]; exact hs)
      (by rw [timeComponent_smul_timeUnitVec]; linarith)
    have hleft : s • FieldFormConditions.timeUnitVec - (3 * η) • FieldFormConditions.timeUnitVec =
        (s - 3 * η) • FieldFormConditions.timeUnitVec :=
      (sub_smul _ _ _).symm
    have hright : (2 * s - 3 * η) • FieldFormConditions.timeUnitVec -
        s • FieldFormConditions.timeUnitVec = (s - 3 * η) • FieldFormConditions.timeUnitVec := by
      rw [← sub_smul]
      congr 1
      ring
    rw [hleft, hright] at hform
    exact hform
  have hchoice : ∀ s : ℝ, 0 < s →
      0 < min 1 s / 3 ∧ min 1 s / 3 ≤ 1 ∧ 3 * (min 1 s / 3) ≤ s := by
    intro s hs
    have hpos : 0 < min 1 s := lt_min one_pos hs
    have hle1 : min 1 s ≤ 1 := min_le_left _ _
    have hles : min 1 s ≤ s := min_le_right _ _
    exact ⟨by linarith, by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s a hs ha
    obtain ⟨hη0, hη1, hη3⟩ := hchoice s hs
    set η := min 1 s / 3
    have hshift : 0 ≤ ((s - 3 * η) • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx := by
      rw [timeComponent_smul_timeUnitVec]
      linarith
    have ha' : 0 ≤ (a • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx := by
      rw [timeComponent_smul_timeUnitVec]
      exact ha.le
    have hsumL : (s + a - 3 * η) • FieldFormConditions.timeUnitVec =
        (a • FieldFormConditions.timeUnitVec) + (s - 3 * η) • FieldFormConditions.timeUnitVec := by
      rw [← add_smul]
      congr 1
      ring
    have hsumR : (s + a - 3 * η) • FieldFormConditions.timeUnitVec =
        ((s - 3 * η) • FieldFormConditions.timeUnitVec) + a • FieldFormConditions.timeUnitVec := by
      rw [← add_smul]
      congr 1
      ring
    have hL := hmul _ _ ha' hshift
    have hR := hmul _ _ hshift ha'
    rw [← hsumL] at hL
    rw [← hsumR] at hR
    rw [hmid s η hη0 hη1 hη3, hmid (s + a) η hη0 hη1 (by linarith),
      ← realWickPoint_smul_timeUnitVec]
    calc _ = (FieldForms.spectralTranslation E
              (InsertedFieldForm.realWickPoint (a • FieldFormConditions.timeUnitVec)) *
            FieldForms.spectralTranslation E
              (InsertedFieldForm.realWickPoint ((s - 3 * η) • FieldFormConditions.timeUnitVec))) *
              InsertedFieldForm.smoothedFieldOp σ E η 0 *
            (FieldForms.spectralTranslation E
              (InsertedFieldForm.realWickPoint ((s - 3 * η) • FieldFormConditions.timeUnitVec)) *
              FieldForms.spectralTranslation E
                (InsertedFieldForm.realWickPoint (a • FieldFormConditions.timeUnitVec))) := by
          simp only [mul_assoc]
      _ = _ := by rw [hL, hR]
  · intro s hs
    obtain ⟨hη0, hη1, hη3⟩ := hchoice s hs
    have hm : 0 < min 1 s := lt_min one_pos hs
    have hshift : 0 ≤ ((s - 3 * (min 1 s / 3)) • FieldFormConditions.timeUnitVec)
        TimeAxis.timeIdx := by
      rw [timeComponent_smul_timeUnitVec]
      linarith
    have hv := ((hKernel σ E p C hcond _ hη0 hη1).2.1 0
      (by rw [Pi.zero_apply, abs_zero]; linarith)).2
    have hTs := hcontr _ hshift
    rw [hmid s _ hη0 hη1 hη3]
    show ‖_‖ ≤ _
    have hv' : ‖InsertedFieldForm.smoothedFieldOp σ E (min 1 s / 3) 0‖ ≤
        InsertedFieldForm.smoothedFieldConst C * (min 1 s / 3) ^ (-p - 5) := hv
    have hbound : ‖FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint
          ((s - 3 * (min 1 s / 3)) • FieldFormConditions.timeUnitVec)) *
        InsertedFieldForm.smoothedFieldOp σ E (min 1 s / 3) 0 *
          FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint
            ((s - 3 * (min 1 s / 3)) • FieldFormConditions.timeUnitVec))‖ ≤
        ‖InsertedFieldForm.smoothedFieldOp σ E (min 1 s / 3) 0‖ := by
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_left hTs (norm_nonneg _)).trans ?_
      rw [mul_one]
      refine (norm_mul_le _ _).trans ?_
      exact (mul_le_mul_of_nonneg_right hTs (norm_nonneg _)).trans (by rw [one_mul])
    refine hbound.trans (hv'.trans (le_of_eq ?_))
    rw [div_three_rpow hm, InsertedFieldForm.smoothedFieldConst, InsertedFieldForm.formConstant,
      InsertedFieldForm.formExponent]
    ring
  · intro c s y hs hsy hsc
    obtain ⟨hη0, hη1, hη3⟩ := hchoice s hs
    set η := min 1 s / 3
    have hshift : 0 ≤ ((s - 3 * η) • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx := by
      rw [timeComponent_smul_timeUnitVec]
      linarith
    have hx : 0 ≤ (y - s • FieldFormConditions.timeUnitVec) TimeAxis.timeIdx := by
      rw [Pi.sub_apply, timeComponent_smul_timeUnitVec]
      linarith
    have hx' : 0 ≤ ((c - s) • FieldFormConditions.timeUnitVec - y) TimeAxis.timeIdx := by
      rw [Pi.sub_apply, timeComponent_smul_timeUnitVec]
      linarith
    have hL := hmul _ _ hx hshift
    have hR := hmul _ _ hshift hx'
    have hsumL : y - s • FieldFormConditions.timeUnitVec +
        (s - 3 * η) • FieldFormConditions.timeUnitVec =
          y - (3 * η) • FieldFormConditions.timeUnitVec := by
      rw [sub_smul]
      abel
    have hsumR : (s - 3 * η) • FieldFormConditions.timeUnitVec +
        ((c - s) • FieldFormConditions.timeUnitVec - y) =
          (c - 3 * η) • FieldFormConditions.timeUnitVec - y := by
      rw [sub_smul, sub_smul, sub_smul]
      abel
    rw [hsumL] at hL
    rw [hsumR] at hR
    rw [hG.eq_conj c η y hη0 hη1 (by linarith) (by linarith), hmid s η hη0 hη1 hη3, ← hL, ← hR]
    simp only [mul_assoc]
end YangMills.Construction.MidpointOperators
end
