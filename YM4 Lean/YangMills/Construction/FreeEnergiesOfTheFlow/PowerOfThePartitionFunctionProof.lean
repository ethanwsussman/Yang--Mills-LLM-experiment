import YangMills.Construction.FreeEnergiesOfTheFlow.GrowthOfTheFreeEnergy
import YangMills.Construction.FreeEnergiesOfTheFlow.PowerOfThePartitionFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings
open YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.WeightedResponses
theorem partitionPowerBound_of_volumeScaling (hScaling : freeEnergyVolumeScaling) : partitionPowerBound := by
  obtain ⟨r, hr, h⟩ := hScaling
  refine ⟨r, hr, fun T hT hC hrt => ?_⟩
  obtain ⟨y₀, hy⟩ := h T hT hC hrt
  refine ⟨y₀, fun y hy₀ hS => ?_⟩
  obtain ⟨C, nS, hC0, hnS, hm⟩ := hy y hy₀ hS
  refine ⟨C, nS, hC0, hnS, fun β t hrr n n' _ _ hb hb' hnn hs => ?_⟩
  obtain ⟨hZ, hZ', habs⟩ := hm β t hrr n n' hb hb' hnn hs
  have hle := (abs_le.mp habs).1
  have hlog : (n' : ℝ) ^ 4 / (n : ℝ) ^ 4 * Real.log (torusPartition (T.stepParameters y) β t n) ≤
      C * (1 + Real.log (flowCoupling (T.stepParameters y) β t)) * (n' : ℝ) ^ 4 +
        Real.log (torusPartition (T.stepParameters y) β t n') := by linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log hZ', mul_comm ((n' : ℝ) ^ 4 / (n : ℝ) ^ 4), ← Real.rpow_def_of_pos hZ] at hexp
  exact hexp
end YangMills.Construction.FreeEnergies
end
