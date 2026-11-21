import YangMills.Construction.SummableBoundsOfTheFlow.ExponentReadAbove
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Interpolation
open BlockAverages ColdStepAtMirrorFrames
def interpolatedExponentBoundsAtTopStatement : Prop :=
  ∀ (F : BlockFrame) (s a ρA ρ x κ κ₂ δ₂ Ct ω C Cg Ch Wt Dm : ℝ) (m N : ℕ) (Kf : ℕ → ℝ) (Dk : ℕ → ℕ → ℝ)
    (V : F.GaugeField F.top),
    Nonempty ↥(chordBonds (finiteCells F)) → 0 < ρ → 0 < κ → 2 ^ 10 * κ ≤ δ₂ → 1 ≤ x → 0 ≤ Ct * ω →
    x * (Ct * ω) ≤ 1 → 0 ≤ Cg → 0 ≤ Ch → 0 ≤ Dm → (∀ l j, l ≤ 3 → j ≤ 3 → Dk l j ≤ Dm) →
    (∀ z : F.Cell, (cellChordBonds z).card ≤ N) →
    (∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(δ₂ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Wt) →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      HasInterpolationKernels s a ρA κ κ₂ δ₂ x m Kf Dk V η) →
    InterpolatedSlopeSmall s a ρA δ₂ Ct ω x m V →
    (∀ (η : StepVariable (finiteCells F)) (c₀ : F.Site F.top × Fin 4), (∀ b, ‖η b‖ < ρ) →
      c₀ ∈ innerBonds (finiteCells F) F.top →
      |haarGapExcess a x (interpolatedField s a ρA m V η) c₀| ≤ Cg) →
    (∀ (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))), (∀ b, ‖η b‖ < ρ) →
      |haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2)| ≤ Ch) →
    (N : ℝ) * ρ + (Wt + N) / 2 * Dm + 4 * (Cg + Dm) + N * (Ch + Dm) ≤ C →
    Dm * (N + 1) + 1 + Dm * (Wt + 1) + 4 * Dm + N * Dm ≤ C →
    (N : ℝ) * ρ * Dm + 2 * Dm + 4 * Dm + N * Dm ≤ C →
    InterpolatedExponentBounds s a ρA ρ x κ C m V
end Interpolation
end YangMills.Construction
end
