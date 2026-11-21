import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def minimizerExcessSumZero : Prop :=
  ∀ (F : BlockFrame) (a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top), 0 ≤ a → Odd F.blockSide →
    (∀ i, 2 ≤ F.extent i) →
    (∃ w, IsMinimizingChart a (finiteCells F) V ρA w) →
    ∑ Y ∈ finiteCells F, frameDensity true a ρA x m Y V = 0
end Interpolation
end YangMills.Construction
end
