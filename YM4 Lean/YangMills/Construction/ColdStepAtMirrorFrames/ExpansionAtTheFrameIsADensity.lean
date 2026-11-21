import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAtTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def expansionAtFrameIsLocalDensityStatement : Prop :=
  ∀ T : StepParameters, T.IsOrdered → 64 ≤ T.n₀ → expansionTransportAt T →
    (∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top) (star : Bool), T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → ∃ C : ℝ,
        FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ T.chainParams.Kk (frameRadius x) V) →
    ExpansionAtFrameIsLocalDensityAt T
end YangMills.Construction.ColdStepAtMirrorFrames
end
