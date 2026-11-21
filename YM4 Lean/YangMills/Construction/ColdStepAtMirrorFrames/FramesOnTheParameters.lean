import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def FrameBoundsForParameters (T : StepParameters) : Prop :=
  ∃ Cf C : ℝ, 0 < Cf ∧ 1 ≤ C ∧ Cf ≤ T.Ct ∧ C ≤ T.Ct ∧ 2 ^ 40 ≤ T.L ∧ 64 ≤ T.n₀ ∧ T.κ ≤ 1 ∧ T.σ ≤ 1 ∧
    C * T.σ + T.σ / 64 ≤ 1 / (64 * (T.L : ℝ)) ∧ C * T.σ + 5 * (T.L : ℝ) * (T.σ / 64) ≤ 1 / 2 ∧
    5 / 4 * T.σ ≤ T.chainParams.σA ∧ 1 ≤ T.coupling ∧ 2 ≤ T.a * T.coupling ∧
    ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
      IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      FrameBoundsAt T.a T.L T.chainParams Cf C T.σ T.κ x (frameRadius x) t T.n₀ F V
def FrameBoundsEventually : Prop := EventuallyInParameters FrameBoundsForParameters
end YangMills.Construction.ColdStepAtMirrorFrames
end
