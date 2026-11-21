import YangMills.Construction.ClusterExpansionOfAStep.BottomOfTheChainIsWilsonsMeasure
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionReturnsAtDrawnParameters
import YangMills.Construction.ClusterExpansionOfAStep.FlowWhereTheExpansionReturns
import YangMills.Construction.ColdStepAtMirrorFrames.DensitiesOfTheStep
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawOfTheTrajectoryIsTheLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
theorem flowIsChainLaw_of_expansionReturns (hret : StepReturn.ExpansionHoldsAtAdmissibleParameters)
    (hflow : ClusterExpansionOfAStep.FlowWhereExpansionReturns)
    (hdens : ColdStepAtMirrorFrames.stepDensityBoundsStatement)
    (hbot : ClusterExpansionOfAStep.bottomChainLawIsWilsonGibbsStatement) :
    flowIsChainLaw := by
  obtain ⟨floorL, ceilRt, ceilσ, floorN, floorCs, h1, h2, hT⟩ := hret
  obtain ⟨C₀, hrun⟩ := hflow
  refine ⟨⟨ColdStepAtMirrorFrames.DensityConditionsAt, floorL, fun _ => C₀, ceilRt, ceilσ, floorN, floorCs,
    fun _ => 0⟩, ⟨hdens, h1, h2⟩, fun T hD hM => ?_⟩
  obtain ⟨y₀, f⟩ := hT T hD hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge hM.holds
  refine ⟨max y₀ T.floorMin, fun y hy => ?_⟩
  have hymin : T.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hadm := hD.fits y hymin
  obtain ⟨hl, hr⟩ := hrun _ hadm hM.derivBound_ge (f y (le_trans (le_max_left _ _) hy))
  exact ⟨hymin, hadm, hl, fun β t n m K _ h₁ h₂ => hbot _ β _ t n m K _ h₁ h₂ (hl β t n).1,
    fun β hβ => (hr β hβ).1, fun β hβ => (hr β hβ).2.1, fun β hβ => (hr β hβ).2.2⟩
end YangMills.Construction.TotalDensities
end
