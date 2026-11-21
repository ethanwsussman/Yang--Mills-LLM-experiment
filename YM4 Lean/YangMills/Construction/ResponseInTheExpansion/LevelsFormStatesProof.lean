import YangMills.Construction.ResponseInTheExpansion.LevelsFormStates
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
private theorem isWellPosed_of_onParameters {T : RenormalizationStepParameters.ParameterAssignment} (hT : T.Admissible) {y : ℝ}
    (hy₀ : T.floorMin ≤ y) (hy₁ : 1 ≤ y) {R : StepSettings.StepSetup}
    (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B) (hsym : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
theorem stagesAreWellPosed_of_floors (hFl : StepFloors.EventuallyFloorConditions) : StagesAreWellPosed := by
  intro T hT
  have hC : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT _ 1 hC one_pos
  refine ⟨max (max T.floorMin yF) 1, fun y hy K β hL z₀ _ s hst t ht => ?_⟩
  have h₁ : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have h₂ : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have h₃ : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hS := hst t ht
  have hon := hS.onFamily.onFamily
  exact isWellPosed_of_onParameters hT h₁ h₃ hon hS.onFamily.abs_sub_le hS.isSymmetricWeight
    (hyF _ (h₂.trans hon.le_coupling))
end YangMills.Construction.ResponseInTheExpansion
end
