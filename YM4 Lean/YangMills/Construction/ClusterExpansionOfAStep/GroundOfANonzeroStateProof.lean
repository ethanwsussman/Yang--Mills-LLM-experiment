import YangMills.Construction.ClusterExpansionOfAStep.GroundHasWeightAtItsFrames
import YangMills.Construction.ClusterExpansionOfAStep.GroundOfANonzeroState
import YangMills.Construction.ClusterExpansionOfAStep.HotGroundIsOfItsState
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfPointsOfWeight
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
theorem nonvanishingStateHotGround_proof (hB : StepGas.HullStateIsHotCase)
    (hS : SettingAdmissibleOfHasWeight) (hW : StepGas.GroundWeightAtEmpty) (hH : HotGroundIsOverState) :
    NonvanishingStateHotGround := by
  intro T hT
  obtain ⟨y₁, h1⟩ := hB T hT
  obtain ⟨y₂, h2⟩ := hS T hT
  obtain ⟨y₃, h3⟩ := hW T hT
  refine ⟨max y₁ (max y₂ y₃), fun y hy R hOn hf hx n _ hb V q hh hΦ => ?_⟩
  have hy₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hhot := h1 y hy₁ R hOn hf n hb V q hh hΦ
  have hG : (StepGas.hotCaseGround R V q).IsAdmissibleGround := Or.inr hhot
  have hset : (StepGas.hotCaseGround R V q).groundSetting.IsAdmissible := by
    refine h2 y hy₂ R hOn hx n _ hG StepGas.GasFamily.empty ?_ 0 (h3 y hy₃ R hOn hx n _ hG)
    exact ⟨fun θ h => by simp [StepGas.GasFamily.Occupies, StepGas.GasFamily.empty] at h, fun θ _ h => by
      simp [StepGas.GasFamily.Occupies, StepGas.GasFamily.empty] at h⟩
  exact hH R hf n V q hhot hset
end YangMills.Construction.ClusterExpansionOfAStep
end
