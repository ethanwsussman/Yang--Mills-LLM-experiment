import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ReferenceDensity
def chartedEnergyAtMinimizerRegular : Prop :=
  EventuallyOrdered fun T =>
    ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffOn ℝ 2 (chartedEnergyAtMinimizer T.a T.ρA V) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      fderiv ℝ (chartedEnergyAtMinimizer T.a T.ρA V) 0 = 0 ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → ∀ c ∈ innerBonds (finiteCells F) F.top,
        0 < ‖contourAverage (fieldAboveFrame true T.a T.ρA 0 V η) c‖) ∧
      0 < T.lam ∧ ∀ η u : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        T.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAtMinimizer T.a T.ρA V) η u u
end ReferenceDensity
end YangMills.Construction
end
