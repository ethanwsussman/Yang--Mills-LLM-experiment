import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Estimates
def JointlyContDiffOnBallsOfDisplacements : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (V : F.GaugeField F.top) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ),
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
        (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions), (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
        ContDiffAt ℝ 3 (jointDisplacement G η V b u c X) 0) →
    JointlyContDiffOnBalls ρ V G
end Estimates
end YangMills.Construction
end
