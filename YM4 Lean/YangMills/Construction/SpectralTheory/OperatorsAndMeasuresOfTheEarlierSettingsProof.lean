import YangMills.Construction.SpectralTheory.BoundedOperatorsOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.CommutingBoundedOperatorsOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.MeasuresOnABorelSetOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.MeasuresOnRealSpaceOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.OperatorsAndMeasuresOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.OperatorsInTheSpaceOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.SpectralMeasuresOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SettingsComparison
theorem allSettingsAgree_of (hBdd : BoundedOpsAgreeForAllSpaces)
    (hUnbdd : UnboundedOpsAgreeForAllSpaces)
    (hBorel : BorelSetMeasuresAgreeForAllSpaces)
    (hFull : FullSpaceMeasuresAgreeForAllSpaces)
    (hSpec : SpectralMeasuresAgreeForAllSpaces)
    (hComm : CommutingBoundedOpsAgreeForAllSpaces) : AllSettingsAgree :=
  fun H _ _ _ => ⟨hBdd H, hUnbdd H, fun n X h₁ h₂ h₃ => hBorel H n X h₁ h₂ h₃,
    fun n _ => hFull H n, hSpec H, hComm H⟩
end YangMills.Construction.SettingsComparison
