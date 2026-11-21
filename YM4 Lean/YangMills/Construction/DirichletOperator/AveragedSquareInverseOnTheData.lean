import YangMills.Construction.DirichletOperator.SiteOperatorsOnTheData
import YangMills.Construction.RegionSequence.GaugeConditionProjections
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.TorusDataComparison
def AvgGreenSqInvAgreesClaim : Prop :=
  ∀ (𝒮 : NestedRegions) (M R₁ : ℕ) (h : 𝒮.IsTorusData M R₁)
    (B : YangMills.Construction.Weighted.SeparatedChain h.toTorusData),
    𝒮.IsGapSeparated M R₁ → (𝒮.Ω 0).Nonempty → B.stage = 𝒮.Ω →
    NestedRegions.AgreesWithTorusData B →
    ∀ (ω : 𝒮.Coarse) (ω' : B.LayerFn), EqOnLayerSites B ω ω' →
      EqOnLayerSites B (NestedRegions.avgGreenSqInv ω) (Ring.inverse B.avgGreenSq ω')
end YangMills.Construction.RegionSequence.TorusDataComparison
