import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveAreAlongLists
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace IteratedDerivative
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
def rotatedEvalContDiffOfDisplacements : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (n : ℕ),
    (∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)),
      (∀ i, ‖u i‖ = 1) → ContDiffAt ℝ (n : WithTop ℕ∞) (jointDisplacement G η V b u c X) 0) →
    ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval G V c X) (η, 0)
end IteratedDerivative
end YangMills.Construction
end
