import YangMills.Construction.RunningCouplingSlope.LongWaves
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def NormaliserHessianOnLongWaves : Prop :=
  ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ (n₀ : ℕ) (m : ℤ) (t : ℝ),
      t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) → |t| < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ A B : edgeFormSpace L n k k, IsPlaneWavePair L n k t A B →
          |normaliserCosineSum L n k t -
              ((2 * (L : ℝ) ^ n) ^ 4)⁻¹ *
                (normaliserHessianAtResponse L n k A + normaliserHessianAtResponse L n k B)| ≤
            C * |t| ^ 3 + ε
end YangMills.Construction.RunningCouplingSlope
end
