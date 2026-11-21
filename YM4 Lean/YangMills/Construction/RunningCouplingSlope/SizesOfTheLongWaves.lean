import YangMills.Construction.RunningCouplingSlope.LongWaves
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Tower.CriticalBranchResponse
def LongWaveSizeBounds : Prop :=
  ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ c r : ℝ, 0 ≤ c ∧ 0 < r ∧ ∀ (n₀ : ℕ) (m : ℤ) (t : ℝ),
      t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) → |t| < r → ∀ᶠ n in atTop,
        ∃ C S : edgeFormSpace L n k k, IsPlaneWavePair L n k t C S ∧
          ∀ B ∈ ({C, S} : Set (edgeFormSpace L n k k)),
            topFormNormSq B ≤ c * (2 * (L : ℝ) ^ n) ^ 4 ∧
            topFormNormSq (periodicDefect L n k B) ≤ c * (2 * (L : ℝ) ^ n) ^ 4 * t ^ 4 ∧
            tripleNormSq (backgroundOnlyTriple (meshScaledResponse L n k B)) ≤ c * (2 * (L : ℝ) ^ n) ^ 4
end YangMills.Construction.RunningCouplingSlope
end
