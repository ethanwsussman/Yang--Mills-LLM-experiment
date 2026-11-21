import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields StepSettings ColdStepAtMirrorFrames
def liePointBallVolume (ρ : ℝ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ)).toReal
def LocalIntegralLeBallVolume : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (s : ChartSetting R n) (N : Finset (TorusSite n)) (M : ℝ),
    0 < R.ballRadius → ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn →
    (∀ ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3), (∀ b, coordNorm (ζ b) < R.ballRadius) →
      -(s.localPotential N ζ) ≤ M) →
    s.localIntegral N ≤ liePointBallVolume R.ballRadius ^ (s.freeNear N).card * Real.exp M
end YangMills.Construction.ClusterExpansionOfAStep
end
