import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
def topOrderNearBlockAt (T : StepParameters) (N : ℕ) (Cn : ℕ → ℝ) : Prop :=
  ∀ (x : ℝ) (t k : ℕ) (e : ℕ → ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (s : ℝ) (η : StepVariable (finiteCells F)) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    T.coupling ≤ x → 3 ≤ k → k ≤ 6 → (∀ j, 0 ≤ e j) →
    HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
    AreUnitVectors X → bondSpan Y c < N →
    |bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y η) V c X| ≤
      (2⁻¹ ^ 9 * e k + Cn k * runningMax e (k - 1)) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
def topOrderNearBlockStatement : Prop :=
  ∃ Cn : StepParameters → ℕ → ℕ → ℝ, (∀ T N k, 0 < Cn T N k) ∧ ∀ Nf : StepParameters → ℕ,
    EventuallyInParameters fun T => topOrderNearBlockAt T (Nf (rateParameters T))
      (Cn (rateParameters T) (Nf (rateParameters T)))
end Interpolation
end YangMills.Construction
end
