import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveAreAlongLists
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def interpolatedBlockExponentSmoothStatement : Prop :=
  ∀ (F : BlockFrame) (s a ρA ρ x κ κ₂ δ₂ : ℝ) (m : ℕ) (Kf : ℕ → ℝ) (Dk : ℕ → ℕ → ℝ) (V : F.GaugeField F.top)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    Nonempty ↥(chordBonds (finiteCells F)) →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → HasInterpolationKernels s a ρA κ κ₂ δ₂ x m Kf Dk V η) →
    (∀ b, ‖η b‖ ≤ ρ) → AreUnitVectors X →
    ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (IteratedDerivative.rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X) (η, 0)
end Interpolation
end YangMills.Construction
end
