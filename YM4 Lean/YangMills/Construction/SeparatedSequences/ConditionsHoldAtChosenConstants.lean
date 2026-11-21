import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses
def OperatorBoundsHoldAtConstants : Prop :=
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (operatorConstantsAt L).Pos ∧
      (L : ℝ) ^ 2 ≤ YangMills.Construction.SeparatedSequences.CombinedConstants.blockLower L ∧
        12 * (L : ℝ) ≤ (L : ℝ) ^ 2) ∧
  ∀ s : OperatorSetting, s.data.MeetsSizeLowerBounds → s.OperatorBounds (operatorConstantsAt s.data.L)
end YangMills.Construction.SeparatedClasses
end
