import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
def PartialGaugeField.IsValuedOnSymmetricSupport {L m : ℕ} {j : ℤ} (𝒢 : Set ComplexMatrix2)
    (V : PartialGaugeField L m j) : Prop :=
  IsReversalClosed V.support ∧ IsGaugeField 𝒢 V.support V.field
def AveragesAndIteratesAreGaugeFields : Prop :=
  ∀ (L m K j : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → j < K →
    ∀ ℬ : Set (BondAtLevel L m K j), IsReversalClosed ℬ →
      (∀ (U : BondAtLevel L m K j → ComplexMatrix2) (c : BondAtLevel L m K (j + 1)),
        IsGaugeField compactGaugeGroup ℬ U →
          (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) ⊆ ℬ →
            onSetElseOne (bondsInDoubleBlock c) U ∈ gaugeFieldsAtLevel L m K j ∧
              ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K j)),
                onSetElseOne (bondsInDoubleBlock c) U b = U b) ∧
      (∀ U : BondAtLevel L m K j → ComplexMatrix2, IsGaugeField compactGaugeGroup ℬ U →
        (realPartialBlockAverage (Averaging.smoothingRadius L)
          (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K j)) :
          PartialGaugeField L m (levelDepth K (j + 1))).IsValuedOnSymmetricSupport
            compactGaugeGroup) ∧
      (∀ U : BondAtLevel L m K j → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ U →
        (complexPartialBlockAverage (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K j)) :
          PartialGaugeField L m (levelDepth K (j + 1))).IsValuedOnSymmetricSupport
            complexGaugeGroup) ∧
      ∀ i : ℕ, j + i ≤ K →
        (∀ U : BondAtLevel L m K j → ComplexMatrix2, IsGaugeField compactGaugeGroup ℬ U →
          (partialBlockAverageIter (K := K) (Averaging.smoothingRadius L) j
            (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K j)) i).IsValuedOnSymmetricSupport
              compactGaugeGroup) ∧
        (∀ U : BondAtLevel L m K j → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ U →
          (complexPartialBlockAverageIter (K := K) j
            (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K j)) i).IsValuedOnSymmetricSupport
              complexGaugeGroup)
end YangMills.Construction.PeriodicLattice
