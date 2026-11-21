import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.FormsOfCombsTreesGaugesAndProjectionsInAFrame
import YangMills.Construction.Lattice.TowerAxialGaugeOutsideNodesInAFrame
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.AxialTowerUniqueness
variable {L m : ℕ}
def CombHolonomiesTrivial (r : SignedFrame) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ (n : ℕ) (z : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n),
    IsChainTriple K k Ω n z x →
      AndAveragesFormed (Ω 0) {c | c ∈ framedBlockComb r z x}
        (pathHolonomy (regionBlockField n (Ω 0) U) (framedBlockComb r z x) = 1)
structure IsAxialGaugeBackground (r : SignedFrame) (α₀ : ℝ) (K k e s : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (U₀ : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  side_pos : 0 < m
  landau : IsLandauBackground (Averaging.smoothingRadius L) (finestMeshInLevelUnits L k) α₀ K k e s Ω U₀
  combs_trivial : CombHolonomiesTrivial r K k Ω U₀
def BothSmallLandauPairs (r : SignedFrame) (α : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) {K : ℕ}
    (U₀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (p q : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) ×
      (SiteAtLevel L m K 0 → Matrices.ComplexMatrix2)) : Prop :=
  FrameForms.IsSmallFieldLandauPairRot r (Averaging.smoothingRadius L) (finestMeshInLevelUnits L k)
      α k Ω U₀ U p ∧
    FrameForms.IsSmallFieldLandauPairRot r (Averaging.smoothingRadius L) (finestMeshInLevelUnits L k)
      α k Ω U₀ U q
def IsUniquenessThreshold (L : ℕ) (c : ℝ) : Prop :=
  ∀ (m K k e s : ℕ) (r : SignedFrame) (α₀ α : ℝ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2), 2 ≤ e + s → 0 < α₀ → α₀ ≤ c → 0 < α →
    α ≤ c → IsAxialGaugeBackground r α₀ K k e s Ω U₀ → U ∈ gaugeFieldsInside K (Ω 0) →
    CombHolonomiesTrivial r K k Ω U →
    ∀ p q : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) ×
        (SiteAtLevel L m K 0 → Matrices.ComplexMatrix2),
      BothSmallLandauPairs r α k Ω U₀ U p q → p = q
end YangMills.Construction.PeriodicLattice.AxialTowerUniqueness
