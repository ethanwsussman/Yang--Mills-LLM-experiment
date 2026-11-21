import YangMills.Construction.ColdStepAtMirrorFrames.DensityHypothesesAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def MeansContDiffThreeAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f => ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * T.σ) V →
    ContDiffThreeAlongBonds (T.interactionFamily x f F Y) V ∧
      ContDiffThreeAlongBonds (T.expansionFamily x f F Y) V
def meansContDiffThree : Prop := EventuallyInParameters MeansContDiffThreeAt
end ColdStepAtMirrorFrames
end YangMills.Construction
end
