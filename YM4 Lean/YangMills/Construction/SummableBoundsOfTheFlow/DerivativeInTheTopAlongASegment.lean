import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.Estimates
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
def fieldDerivAlongSegmentStatement : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (V : F.GaugeField F.top) (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (D : ↥(chordBonds (finiteCells F)) → ℝ) (η : StepVariable (finiteCells F)),
    JointlyContDiffOnBalls ρ V G → k ≤ 2 →
    (∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → ∀ (b : ↥(chordBonds (finiteCells F)))
      (u : EuclideanSpace ℝ (Fin 3)), ‖u‖ = 1 → |jointMixedDeriv G ζ V ![b] ![u] e X| ≤ D b) →
    (∀ b, ‖η b‖ ≤ ρ) →
    |fieldDeriv G V e X η - fieldDeriv G V e X 0| ≤ ∑ b, ‖η b‖ * D b
end YangMills.Construction.Estimates
end
