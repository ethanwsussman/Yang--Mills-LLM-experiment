import YangMills.Construction.SpectralTheory.PreliminarySettingsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SettingsComparison
def FullSpaceMeasuresAgreeForAllSpaces : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) [NeZero n], SettingsComparison.FullSpaceMeasuresAgree E n
end YangMills.Construction.SettingsComparison
