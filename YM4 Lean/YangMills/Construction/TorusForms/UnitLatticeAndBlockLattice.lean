import YangMills.Construction.TorusForms.BlocksCorridorsAveragesTrees
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin
open YangMills.Construction.Lattice
class PeriodsMultipleOfBlock (S : LatticeParameters) (ℓ : Fin S.d → ℝ) : Prop where
  multiple : ∀ μ, ∃ N : ℕ, 2 ≤ N ∧ ℓ μ = (N : ℝ) * (S.L : ℝ)
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ}
theorem PeriodsMultipleOfBlock.blockSize_pos (S : LatticeParameters) : (0 : ℝ) < (S.L : ℝ) := by
  exact_mod_cast lt_of_lt_of_le two_pos S.two_le_L
theorem PeriodsMultipleOfBlock.isBlockSpacing_one [h : PeriodsMultipleOfBlock S ℓ] :
    IsBlockSpacing S 1 ℓ 1 (S.L : ℝ) where
  spacing_eq := by simp
  ratio_mem μ := by
    obtain ⟨N, hN, hl⟩ := h.multiple μ
    refine ⟨N, hN, ?_⟩
    rw [hl, mul_div_assoc, div_self (PeriodsMultipleOfBlock.blockSize_pos S).ne', mul_one]
instance PeriodsMultipleOfBlock.unitSpacing [h : PeriodsMultipleOfBlock S ℓ] :
    IsCommensurateSpacing ℓ (1 : ℝ) where
  periods_pos μ := by
    obtain ⟨N, hN, hl⟩ := h.multiple μ
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le two_pos hN
    rw [hl]
    exact mul_pos hN' (PeriodsMultipleOfBlock.blockSize_pos S)
  spacing_pos := one_pos
  ratio_mem μ := by
    obtain ⟨N, hN, hl⟩ := h.multiple μ
    refine ⟨N * S.L, Nat.mul_pos (by omega) (by have := S.two_le_L; omega), ?_⟩
    rw [hl, div_one]
    push_cast
    ring
instance PeriodsMultipleOfBlock.blockSpacing [PeriodsMultipleOfBlock S ℓ] :
    IsCommensurateSpacing ℓ (S.L : ℝ) :=
  (PeriodsMultipleOfBlock.isBlockSpacing_one (S := S) (ℓ := ℓ)).isCommensurateSpacing
def unitLatticeCurvature (B : Cochain1 ℓ 1) : Cochain2 ℓ 1 := latticeCurl ℓ 1 B
end YangMills.Construction.BlockSpin
