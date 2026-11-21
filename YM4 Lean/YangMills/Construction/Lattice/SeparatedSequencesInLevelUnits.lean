import YangMills.Construction.Lattice.SettingOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequence
open PeriodicLattice
variable {L m : ℕ}
structure DepthParameters (L m : ℕ) where
  base : Parameters L m
  base_k_eq_one : base.k = 1
  k : ℕ
  k_le_K : k ≤ base.K
namespace DepthParameters
variable (N : DepthParameters L m)
abbrev K : ℕ := N.base.K
abbrev blockExp : ℕ := N.base.blockExp
def toParameters (hk : 1 ≤ N.k) : Parameters L m :=
  { N.base with k := N.k, one_le_k := hk, k_le_K := N.k_le_K }
def eta : ℝ := finestMeshInLevelUnits L N.k
end DepthParameters
structure IsSingleRegion (N : DepthParameters L m) (Ω : ℕ → Set (FourTorus L m)) : Prop where
  isPartitionRegion : IsPartitionRegion (scaledCubeIndex N.K 0 N.blockExp) (Ω 0)
  zero_eq_empty_of_not_hasBlocksAt : ¬N.base.HasBlocksAt 0 → Ω 0 = ∅
  eq_empty_of_pos : ∀ q, 0 < q → Ω q = ∅
structure DepthChain (N : DepthParameters L m) where
  region : ℕ → Set (FourTorus L m)
  exists_chain : ∀ hk : 1 ≤ N.k, ∃ B : Chain (N.toParameters hk), B.region = region
  isSingleRegion_of_k_eq_zero : N.k = 0 → IsSingleRegion N region
end SeparatedSequence
end YangMills.Construction
