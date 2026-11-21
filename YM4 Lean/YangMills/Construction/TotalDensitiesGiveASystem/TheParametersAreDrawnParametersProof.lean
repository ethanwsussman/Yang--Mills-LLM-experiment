import YangMills.Construction.ClusterExpansionOfAStep.ExpansionReturnsAtDrawnParameters
import YangMills.Construction.ColdStepAtMirrorFrames.DensitiesOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheParametersAreDrawnParameters
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
theorem responseParametersToAdmissibleParameters_of_components
    (hR : StepReturn.ExpansionHoldsAtAdmissibleParameters)
    (hW : TorusLumps.WilsonWeightHasExpansion)
    (hC : ColdStepAtMirrorFrames.stepDensityBoundsStatement)
    (hH : WeightedResponses.coldRegimeEstimatesStatement) :
    ResponseParametersToAdmissibleParameters := by
  classical
  intro P hP
  obtain ⟨sideFloor, rateCeil, thresholdCeil, levelFloor, constFloor, h1, h2, hT⟩ := hR
  obtain ⟨Cw, hw⟩ := hW
  choose! L₀ rt₀ C₀ hrt hmain using hP
  refine ⟨⟨fun S => ColdStepAtMirrorFrames.DensityConditionsAt S ∧ WeightedResponses.ColdRegimeEstimatesAt S,
      fun a => max (sideFloor a) (L₀ a), fun a => max Cw (C₀ a),
      fun D => min (rateCeil D) (if 1 ≤ D.coupling then rt₀ D.coupling D else 1), thresholdCeil, levelFloor,
      constFloor, fun _ => 0⟩,
    ⟨ColdStepAtMirrorFrames.EventuallyInParameters.and hC hH, fun D => lt_min (h1 D) ?_, h2⟩,
    fun T hD hM => ?_⟩
  · split_ifs with h
    · exact hrt _ h D
    · exact one_pos
  have ha : 1 ≤ T.coupling := hD.a_ge
  have hon : T.HoldsFrom fun S =>
      ColdStepAtMirrorFrames.DensityConditionsAt S ∧ WeightedResponses.ColdRegimeEstimatesAt S := hM.holds
  obtain ⟨c, nss, hc, hS⟩ := hon
  have hCold : T.ColdStepHolds := ⟨c, nss, hc, fun y hy => (hS y hy).1⟩
  have hHalf : T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt := ⟨c, nss, hc, fun y hy => (hS y hy).2⟩
  have hrt₁ : T.rt ≤ rateCeil T.toChainParameters := le_trans hM.rt_le (min_le_left _ _)
  have hrt₂ : T.rt ≤ rt₀ T.coupling T.toChainParameters := by
    have h := le_trans hM.rt_le (min_le_right _ _)
    have hif : (if 1 ≤ T.toChainParameters.coupling then rt₀ T.toChainParameters.coupling T.toChainParameters
        else 1) = rt₀ T.coupling T.toChainParameters := if_pos ha
    rwa [hif] at h
  obtain ⟨y₁, f₁⟩ := hT T hD (le_trans (le_max_left _ _) hM.side_ge) hrt₁ hM.threshold_le hM.n₀_ge hM.Cs_ge hCold
  obtain ⟨y₂, f₂⟩ := hmain T.coupling ha T.side hD.L_odd (le_trans (le_max_right _ _) hM.side_ge) T rfl rfl hD hCold hHalf
    hrt₂ (le_trans (le_max_right _ _) hM.derivBound_ge)
  refine ⟨max (max y₁ y₂) T.floorMin, fun y hy => ?_⟩
  have hfit := hD.fits y (le_trans (le_max_right _ _) hy)
  exact f₂ y (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy)
    (f₁ y (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy))
    fun β hβ => hw _ hfit (le_trans (le_max_left _ _) hM.derivBound_ge) β hβ
end YangMills.Construction.TotalDensitiesGiveASystem
end
