import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CubesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
structure LargeFieldParameters (c : ChoiceUpToDegreeConstants) (K : ℕ) (x : ℕ → ℝ) :
    Prop where
  factor_admissible : Conventions.IsAdmissibleBlockingFactor c.L
  blockNumber_isPow : IsPositivePowerOf c.L c.blockNumber
  gapNumber_isPow : IsPositivePowerOf c.L c.gapNumber
  M₁_isPow : IsPositivePowerOf c.L c.M₁
  gap_mul_block_le : c.gapNumber * c.blockNumber ≤ c.M₁
  M_isPow : IsPositivePowerOf c.L c.M
  pow_four_mul_le : c.L ^ 4 * c.M₁ ≤ c.M
  two_le_r : 2 ≤ c.r
  one_lt_coupling : ∀ i ≤ K, 1 < x i
def PartitionsFit (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ) (t : ℕ) : Prop :=
  c.M * blockSizeAt c x t ≤ c.L ^ (m + K - t)
end PeriodicLattice.CubesOfStep
end YangMills.Construction
end
