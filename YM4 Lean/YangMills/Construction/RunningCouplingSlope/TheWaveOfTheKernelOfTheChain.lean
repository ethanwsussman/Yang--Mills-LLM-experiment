import YangMills.Construction.RunningCouplingSlope.LongWaves
import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def ChainKernelCosineSum : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (n₀ : ℕ) (m : ℤ) (t : ℝ),
      t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) → ∀ᶠ n in atTop,
        (2 * (L : ℝ) ^ n) ^ 4 * chainCosineSum a ρ L n k t =
          SlopeCoefficient.secondDerivAlong (SlopeCoefficient.chainLogarithm a ρ L k) (2 * L ^ n)
              (planeWaveOnTorus (cosinePhase t)) +
            SlopeCoefficient.secondDerivAlong (SlopeCoefficient.chainLogarithm a ρ L k) (2 * L ^ n)
              (planeWaveOnTorus (sinePhase t))
end YangMills.Construction.RunningCouplingSlope
end
