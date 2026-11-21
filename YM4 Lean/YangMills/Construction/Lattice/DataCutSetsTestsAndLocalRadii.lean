import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure SeparatedChainData (L m : ℕ) where
  K : ℕ
  n : ℕ
  blockExp : ℕ
  gapExp : ℕ
  region : ℕ → Set (FourTorus L m)
  odd_L : Odd L
  thirteen_le_L : 13 ≤ L
  K_pos : 0 < K
  m_pos : 0 < m
  n_le_K : n ≤ K
  L_le_pow_gapExp : L ≤ L ^ gapExp
  six_mul_scale_le_side : 6 * ((L ^ gapExp * L ^ blockExp : ℕ) : ℝ) ≤ sideInLevelUnits L m K n
  isSeparatedChain : IsSeparatedChain K blockExp gapExp 0 n region
  region_eq_empty : ∀ q, n < q → region q = ∅
namespace SeparatedChainData
variable {L m : ℕ} (D : SeparatedChainData L m)
def scale : ℕ := L ^ D.gapExp * L ^ D.blockExp
def scaleData : SeparatedSequences.ScaleData := ⟨D.K, D.n, D.n, D.blockExp, D.n_le_K, D.n_le_K⟩
end SeparatedChainData
end YangMills.Construction.PeriodicLattice
