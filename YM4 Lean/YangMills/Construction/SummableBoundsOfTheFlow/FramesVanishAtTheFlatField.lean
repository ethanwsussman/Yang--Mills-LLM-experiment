import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SummableBounds
open BlockAverages ColdStepAtMirrorFrames
def FramesVanishAtFlat (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (mirror : Bool), T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F →
    (∀ b ∈ chordBonds (finiteCells F),
      stepFrame mirror T.a T.chainParams.ρA (frameRadius x) b (uniformField F F.top) = 0) ∧
    fieldAboveFrame mirror T.a T.chainParams.ρA (frameRadius x) (uniformField F F.top) 0 = uniformField F F.depth
def framesVanishAtFlatStatement : Prop := EventuallyInParameters FramesVanishAtFlat
end YangMills.Construction.SummableBounds
end
