import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open WhitneyScales
open scoped ENNReal
def ShellCenterCountBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ j t : ℕ,
    (1 ≤ j → (setCard {z : IntPoint n | (j, z) ∈ pieceIndexSet n ∧
        (t : ℝ) ≤ configNorm (pieceCenter j z) ∧ configNorm (pieceCenter j z) < t + 1} : ℝ≥0∞) ≤
      ENNReal.ofReal (pieceCountConst n * (1 + (t : ℝ)) ^ (4 * n - 4) *
        whitneyScale j ^ (4 - 4 * (n : ℤ)))) ∧
    (j = 0 → (setCard {z : IntPoint n | (j, z) ∈ pieceIndexSet n ∧
        (t : ℝ) ≤ configNorm (pieceCenter j z) ∧ configNorm (pieceCenter j z) < t + 1} : ℝ≥0∞) ≤
      ENNReal.ofReal (pieceCountConst n * (1 + (t : ℝ)) ^ (4 * n)))
end YangMills.Construction.ConfigurationSpace
end
