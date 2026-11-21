import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def TopExpansionContDiffAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ side : Bool,
      ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
        ContDiffThreeAlongBonds (cellCentredExpansion side T.a T.chainParams.ρA (frameRadius x) f Y η) V
def topExpansionContDiffEventually : Prop := EventuallyInParameters TopExpansionContDiffAt
end ColdStepAtMirrorFrames
end YangMills.Construction
end
