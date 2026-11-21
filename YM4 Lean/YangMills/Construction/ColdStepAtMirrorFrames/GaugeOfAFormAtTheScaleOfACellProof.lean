import YangMills.Construction.ColdStepAtMirrorFrames.GaugeForTemperedWeightsForm
import YangMills.Construction.ColdStepAtMirrorFrames.WeightsOfPositionsAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem weightedGaugeFixingAtCellScale_holds : weightedGaugeFixingAtCellScale := by
  have hK : (1 : ℝ) ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  refine ⟨Real.sqrt (gaugeConstant (Real.exp 4)), Real.sqrt_pos.2 (gaugeConstant_pos hK), ?_⟩
  intro F B z δ hL hcub hδ0 hδ1
  have hext := extent_pos_of_isLargeCubicTorus hcub
  obtain ⟨φ, hφ, hbound⟩ := exists_cellAverage_eq_zero_weightedNormSq_addGradient_le hL hext
    (expWeight δ z) (expWeight δ z) (Real.exp 4) hK
    (isTemperedWeight_expWeight hL hext hδ0.le hδ1 z)
    (fun x a ha b hb c hc d hd => expWeight_sq_le_corner hL hext hδ0.le hδ1 z x a b c d ha hb hc hd)
    (fun k y h hh l hl => expWeight_sq_le_refine hL hext hδ0.le hδ1 z k y h hh l hl) B
  refine ⟨φ, hφ, ?_⟩
  have hcurl := weightedCurlNormSq_nonneg (expWeight δ z) B
  have htop := _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_nonneg (expWeight δ z) (iteratedLineAverage B F.top)
  have hconst := (gaugeConstant_pos hK).le
  have hside : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := by positivity
  have hcell : (cellSide F : ℝ) = (F.blockSide : ℝ) ^ F.top := by
    push_cast
    rfl
  rw [hcell] at hbound
  change Real.sqrt (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq (expWeight δ z) (addGradient B fun y => - φ y)) ≤
    Real.sqrt (gaugeConstant (Real.exp 4)) * (F.blockSide : ℝ) ^ F.top *
      (Real.sqrt (weightedCurlNormSq (expWeight δ z) B) +
        Real.sqrt (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq (expWeight δ z) (iteratedLineAverage B F.top)))
  calc _ ≤ Real.sqrt (gaugeConstant (Real.exp 4) * ((F.blockSide : ℝ) ^ F.top) ^ 2 *
        (weightedCurlNormSq (expWeight δ z) B +
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq (expWeight δ z) (iteratedLineAverage B F.top))) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (gaugeConstant (Real.exp 4)) * (F.blockSide : ℝ) ^ F.top *
        Real.sqrt (weightedCurlNormSq (expWeight δ z) B +
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq (expWeight δ z) (iteratedLineAverage B F.top)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hconst, Real.sqrt_sq hside]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_add_le_sqrt_add_sqrt _ _ hcurl htop) (by positivity)
end YangMills.Construction.ColdStepAtMirrorFrames
end
