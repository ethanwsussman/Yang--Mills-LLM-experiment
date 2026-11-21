import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice
namespace SequenceNorms
variable {L m : ℕ}
structure RegionChain (L m : ℕ) where
  K : ℕ
  n : ℕ
  blockExp : ℕ
  gapExp : ℕ
  n_le_K : n ≤ K
  region : ℕ → Set (FourTorus L m)
  region_eq_empty : ∀ q, n < q → region q = ∅
structure ChainSetting (L m : ℕ) extends RegionChain L m where
  odd_L : Odd L
  thirteen_le_L : 13 ≤ L
  L_le_gapFactor : L ≤ L ^ gapExp
  sq_le_gapSize : L ^ 2 ≤ L ^ gapExp * L ^ blockExp
  m_pos : 0 < m
  one_le_n : 1 ≤ n
  separated : IsSeparatedChain K blockExp gapExp 0 n region
  region_eq_empty_of_not_hasBlocksAt :
    ∀ q ≤ n, ¬-(m : ℤ) ≤ scaledCubeIndex K q blockExp → region q = ∅
  six_gap_le_side : 6 * ((L ^ gapExp * L ^ blockExp : ℕ) : ℝ) ≤ sideInLevelUnits L m K n
namespace RegionChain
variable (D : RegionChain L m)
end RegionChain
end SequenceNorms
end YangMills.Construction
