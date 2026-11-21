import YangMills.Construction.SpectralTheory.PreliminarySettingsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SettingsComparison
def CommutingBoundedOpsAgreeForAllSpaces : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    SettingsComparison.CommutingBoundedOpsAgree E
end YangMills.Construction.SettingsComparison
