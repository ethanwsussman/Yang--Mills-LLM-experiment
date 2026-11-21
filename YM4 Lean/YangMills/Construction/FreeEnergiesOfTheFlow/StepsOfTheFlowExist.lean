import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def flowStepsExist : Prop :=
  HoldsForAdmissibleParameters fun T y => ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor (T.stepParameters y) β t →
    ∃ R : ℕ → StepSettings.StepSetup, ∀ s < t, IsFlowStep T y β s (R s)
end YangMills.Construction.FreeEnergies
end
