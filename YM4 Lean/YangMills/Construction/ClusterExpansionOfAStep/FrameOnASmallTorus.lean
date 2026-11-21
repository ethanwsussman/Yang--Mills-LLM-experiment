import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def FrameCoordOnSmallTorus : Prop :=
  ∀ (ℓ : StepParameters) (ρA : ℝ) (t m n : ℕ) [NeZero n] (V : TorusField n) (b : TorusBond (n * ℓ.side)),
    ¬ 4 * m + 5 < n →
    YangMills.Construction.StepCosts.frameCoord ℓ ρA t m V b =
      YangMills.Construction.StepMarks.minimizerCoord ℓ.coupling ρA ℓ.side t Finset.univ V b
end YangMills.Construction.TorusLumps
end
