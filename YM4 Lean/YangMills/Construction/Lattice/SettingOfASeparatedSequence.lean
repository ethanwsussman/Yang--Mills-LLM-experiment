import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace SeparatedSequence
variable {L m : ℕ}
structure Parameters (L m : ℕ) where
  K : ℕ
  k : ℕ
  blockExp : ℕ
  gapExp : ℕ
  odd_L : Odd L
  thirteen_le_L : 13 ≤ L
  L_le_gapFactor : L ≤ L ^ gapExp
  sq_le_gapSize : L ^ 2 ≤ L ^ gapExp * L ^ blockExp
  m_pos : 0 < m
  one_le_k : 1 ≤ k
  k_le_K : k ≤ K
namespace Parameters
variable (N : Parameters L m)
def HasBlocksAt (q : ℕ) : Prop := -(m : ℤ) ≤ scaledCubeIndex N.K q N.blockExp
end Parameters
structure Chain (N : Parameters L m) where
  region : ℕ → Set (FourTorus L m)
  separated : IsSeparatedChain N.K N.blockExp N.gapExp 0 N.k region
  region_eq_empty_of_not_hasBlocksAt : ∀ q ≤ N.k, ¬N.HasBlocksAt q → region q = ∅
  region_eq_empty : ∀ q, N.k < q → region q = ∅
end SeparatedSequence
end YangMills.Construction
end
