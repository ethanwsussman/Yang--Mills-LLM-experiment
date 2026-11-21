import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Averaging
structure UnitCovarianceSetting (d L K m : ℕ) (G : Submonoid Matrices.ComplexMatrix2) (ℓ : ℝ)
    (blockCount gapCount : ℕ) : Prop where
  dim_eq_four : d = 4
  group_eq_specialUnitary : G = Matrices.ComplexMatrix2.specialUnitary
  odd_blockSize : Odd L
  thirteen_le_blockSize : 13 ≤ L
  cutoff_pos : 0 < K
  exponent_pos : 0 < m
  side_eq : ℓ = PeriodicLattice.torusSide L m
  blockCount_pow : ∃ a : ℕ, blockCount = L ^ a
  gapCount_pow : ∃ a : ℕ, gapCount = L ^ a
  blockSize_le_gapCount : L ≤ gapCount
  blockSize_sq_le : L ^ 2 ≤ gapCount * blockCount
end YangMills.Construction.Averaging
end
