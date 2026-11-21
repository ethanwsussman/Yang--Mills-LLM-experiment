import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
variable {n : ℕ}
def coldFieldAboveFrames (R : StepSetup) [NeZero n] (V : TorusField n)
    (η : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) :
    TorusField (n * R.params.side) :=
  restrictToTorus (n * R.params.side) (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach
    (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) η)
def coldStepMean (R : StepSetup) [NeZero n] (V : TorusField n)
    (H : StepVariable (finiteCells (torusFrame R.params.side R.depth n)) → ℝ) : ℝ :=
  cutoffMean R.ballRadius R.barrierFn (familyLawExponent 1 R.params.coupling R.anchorRadius R.coupling R.frameReach
    (localFamilyOfDensity R.density)
    (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)) H
def coldSettingMeanEqStepMean : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
    ∀ G : TorusField (n * R.params.side) → ℝ,
      weightedMean (chartDensity (coldChartSetting R V)) (fun η => G ((coldChartSetting R V).field η)) =
        coldStepMean R V fun k => G (coldFieldAboveFrames R V k)
end YangMills.Construction.ResponseInTheExpansion
end
