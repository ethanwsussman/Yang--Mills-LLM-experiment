import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def RescaledExponentAgrees : Prop :=
  EventuallyOrdered fun T => ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (f : LocalFamily) (ν l : ℝ) (Y : F.Cell)
      (ζ : StepVariable (finiteCells F)), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      0 < l → l ≤ l₀ → MemScaledBalls T.ballRadius l ζ →
      stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f ν V (l • ζ) = rescaledExponent T.a T.ρA f ν l V ζ ∧
      cellExponent true T.a T.ρA (l⁻¹ ^ 2) 0 Y V (l • ζ) = rescaledCellTerm T.a T.ρA l Y V ζ ∧
      cellQuadratic T.lam (l⁻¹ ^ 2) Y (l • ζ) = T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)),
        if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0
end YangMills.Construction.ScaledVariables
end
