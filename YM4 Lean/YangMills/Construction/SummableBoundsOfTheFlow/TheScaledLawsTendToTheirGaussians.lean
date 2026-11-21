import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def scaledLawsTendToGaussian : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (law : StepLaw)
      (H : ℝ → StepVariable (finiteCells F) → ℝ) (H₀ : StepVariable (finiteCells F) → ℝ) (K : ℝ) (m : ℕ),
      T.IsBoundedFamilyOrderSix e t f → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      StepLaw.IsUnitWeight law → (∀ l : ℝ, 0 < l → l ≤ l₀ → Measurable (H l)) →
      (∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls T.ballRadius l ζ →
        |H l ζ| ≤ K * (1 + ‖ζ‖) ^ m) →
      (∀ ζ : StepVariable (finiteCells F), Filter.Tendsto (fun l => H l ζ) (𝓝[>] 0) (𝓝 (H₀ ζ))) →
      Filter.Tendsto (fun l => rescaledMean T.a T.ρA T.ballRadius T.lam l T.p f law V (H l)) (𝓝[>] 0)
        (𝓝 (gaussianMean T.a T.ρA T.lam f V law H₀))
end YangMills.Construction.ScaledVariables
end
