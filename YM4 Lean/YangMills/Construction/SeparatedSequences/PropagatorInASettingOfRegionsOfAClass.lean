import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.NestedRegionsPropagator
def Claim : Prop :=
  ∀ s : OperatorSetting, s.data.MeetsSizeLowerBounds → ∀ 𝒮, s.IsNestedRegions 𝒮 →
    (Propagator.SequenceOfRegions.chosenConstants s.data.L).Conclusion 𝒮 s.data.blockSize
end YangMills.Construction.SeparatedClasses.NestedRegionsPropagator
end
