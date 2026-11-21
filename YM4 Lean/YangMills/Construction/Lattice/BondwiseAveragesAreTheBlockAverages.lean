import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ComplexIteratesByTheBondwiseMaps
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def PartialGaugeField.IsRestriction {k : ℤ} (W V : PartialGaugeField L m k) : Prop :=
  W.support ⊆ V.support ∧ ∀ v ∈ W.support, W.field v = V.field v
def barePartialBlockAverageIter (ω : ℝ) (V : PartialGaugeField L m (levelDepth K 0)) (i : ℕ) :
    PartialGaugeField L m (levelDepth K i) :=
  cast (by rw [Nat.zero_add]) (partialBlockAverageIter ω 0 V i)
def PartialAveragesAgreeWithBlockAverage.Statement : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ k : ℕ, k < K →
    (∀ U ∈ gaugeFieldsAtLevel L m K k,
      realPartialBlockAverage (Averaging.smoothingRadius L)
          (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K k)) =
          (⟨univ, blockAverage (Averaging.smoothingRadius L) U⟩ :
            PartialGaugeField L m (levelDepth K (k + 1))) ∧
        (blockAverage (Averaging.smoothingRadius L) U :
            BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) ∈
          gaugeFieldsAtLevel L m K (k + 1)) ∧
    (∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ i : ℕ, i ≤ K →
      barePartialBlockAverageIter (Averaging.smoothingRadius L)
          (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i =
        (⟨univ, blockFieldAtLevel (Averaging.smoothingRadius L) i U⟩ :
          PartialGaugeField L m (levelDepth K i)) ∧
      blockFieldAtLevel (Averaging.smoothingRadius L) i U ∈ gaugeFieldsAtLevel L m K i) ∧
    (∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K (k + 1)) X →
      ∀ U : BondAtLevel L m K k → Matrices.ComplexMatrix2,
        IsGaugeField compactGaugeGroup (bondsInside X) U →
      ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (k + 1))),
        (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) ⊆ bondsInside X ∧
        c ∈ (realPartialBlockAverage (Averaging.smoothingRadius L)
          (⟨bondsInside X, U⟩ : PartialGaugeField L m (levelDepth K k))).support ∧
        (realPartialBlockAverage (Averaging.smoothingRadius L)
          (⟨bondsInside X, U⟩ : PartialGaugeField L m (levelDepth K k))).field c =
            blockAverage (Averaging.smoothingRadius L) U c) ∧
    (∀ V : PartialGaugeField L m (levelDepth K k), IsReversalClosed V.support →
      IsGaugeField complexGaugeGroup V.support V.field → ∀ i : ℕ, k + i ≤ K →
      ∀ c : Bond L m (levelDepth K (k + i)),
        (c ∈ (complexPartialBlockAverageIter k V i).support ↔ ComplexPartialDefinedAt k V i c) ∧
        (ComplexPartialDefinedAt k V i c →
          (complexPartialBlockAverageIter k V i).field c = complexPartialValues k V i c)) ∧
    (∀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
      ∀ i : ℕ, i ≤ K → U ∈ complexBlockFieldDomain (K := K) i →
        bareComplexPartialIter (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i =
          (⟨univ, complexBlockFieldAtLevel i U⟩ : PartialGaugeField L m (levelDepth K i))) ∧
    (∀ V W : PartialGaugeField L m (levelDepth K k), IsReversalClosed V.support →
      IsReversalClosed W.support → W.IsRestriction V →
        (IsGaugeField compactGaugeGroup V.support V.field → ∀ i : ℕ, k + i ≤ K →
          (partialBlockAverageIter (Averaging.smoothingRadius L) k W i).IsRestriction
            (partialBlockAverageIter (Averaging.smoothingRadius L) k V i)) ∧
        (IsGaugeField complexGaugeGroup V.support V.field → ∀ i : ℕ, k + i ≤ K →
          (complexPartialBlockAverageIter k W i).IsRestriction
            (complexPartialBlockAverageIter k V i)))
end YangMills.Construction.PeriodicLattice
