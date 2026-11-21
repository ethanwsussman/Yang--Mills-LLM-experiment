import YangMills.Construction.RunningCouplingSlope.LongWaves
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def DifferenceKernelCosineSum : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ (n₀ : ℕ) (m : ℤ) (t : ℝ),
      t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) → ∀ᶠ n in atTop, ∀ C S : edgeFormSpace L n k k,
        IsPlaneWavePair L n k t C S →
        (2 * (L : ℝ) ^ n) ^ 4 * differenceCosineSum a L n k t =
          freeEnergyHessianAtResponse a C - normaliserHessianAtResponse L n k C +
            (freeEnergyHessianAtResponse a S - normaliserHessianAtResponse L n k S)
end YangMills.Construction.RunningCouplingSlope
end
