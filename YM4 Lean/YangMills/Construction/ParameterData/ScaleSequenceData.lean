import YangMills.Construction.ParameterData.FirstPassageOfTheFlow
import YangMills.Construction.ParameterData.FirstPassagesAreData
import YangMills.Construction.ParameterData.RatioOfBetaToTheLogarithmOfTheCutoff
import YangMills.Construction.ParameterData.SlopeAtTheData
import YangMills.Construction.ParameterData.TheCouplingAlongTheLine
import YangMills.Construction.ParameterData.TheCouplingAtADistance
import YangMills.Construction.ParameterData.TheCouplingNearTheFlow
import YangMills.Construction.ParameterData.TheWindowHasMembers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open RenormalizationStepParameters
structure HasTrajectoryData {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y) : Prop where
  passage : FirstPassageExistsAt D
  data : WindowMembersAreDataAt D
  members : passageWindowNonemptyAt D
  line : CouplingAlongLineAt D
  ratio : BetaLogCutoffRatioAt D
  distance : CouplingAtDistanceAt D
  flow : CouplingNearFlowAt D
  slope : CouplingDecreaseAt D
def trajectoryDataStatement : Prop :=
  ∃ Q : ColdStepAtMirrorFrames.StepParameters → Prop, ColdStepAtMirrorFrames.EventuallyInParameters Q ∧
    ∃ (floorL : ℝ → ℕ) (ceilRt : ChainParameters → ℝ) (ceilσ : ChainParameters → ℝ → ℝ)
      (floorN : ChainParameters → ℝ → ℝ → ℕ) (floorCs : ChainParameters → ℝ → ℝ → ℝ) (C₀ : ℝ),
      (∀ D, 0 < ceilRt D) ∧ (∀ D r, 0 < ceilσ D r) ∧
      ∀ T : ParameterAssignment, T.Admissible → floorL T.coupling ≤ T.side → T.rt ≤ ceilRt T.toChainParameters →
        T.threshold ≤ ceilσ T.toChainParameters T.rt → floorN T.toChainParameters T.rt T.threshold ≤ T.n₀ →
        floorCs T.toChainParameters T.rt T.threshold ≤ T.Cs → C₀ ≤ T.derivBound → T.HoldsFrom Q →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∃ D : TrajectoryParameters T y,
          ∀ Bs lam : ℝ, 2 * T.B ≤ Bs → 0 < lam → lam ≤ D.rateBound →
            (D.withShift Bs lam).Admissible ∧ HasTrajectoryData (D.withShift Bs lam)
end YangMills.Construction.TrajectoryData
end
