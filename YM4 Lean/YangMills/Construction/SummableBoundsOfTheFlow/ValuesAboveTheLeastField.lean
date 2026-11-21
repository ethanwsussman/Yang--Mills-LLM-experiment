import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace StepDensities
def valuesAboveFrameBoundedStatement : Prop :=
  EventuallyOrdered fun T => ∃ R₀ : ℝ, 0 ≤ R₀ ∧
    ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (fieldAboveFrame true T.a T.ρA 0 V η) ∧
      (∀ c ∈ innerBonds (finiteCells F) F.top,
        |Real.log ‖contourAverage (fieldAboveFrame true T.a T.ρA 0 V η) c‖| ≤ R₀) ∧
      ∀ b : ↥(chordBonds (finiteCells F)),
        |haarLogRatio (coordsAboveFrame true T.a T.ρA 0 V η b.1.1 b.1.2)| ≤ R₀
end StepDensities
end YangMills.Construction
end
