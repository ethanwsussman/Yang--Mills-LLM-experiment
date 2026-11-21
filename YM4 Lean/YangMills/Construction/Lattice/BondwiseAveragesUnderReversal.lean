import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
def PartialGaugeField.IsReversalInverse {L m : ℕ} {j : ℤ}
    (V : PartialGaugeField L m j) : Prop :=
  IsReversalClosed V.support ∧ ∀ c ∈ V.support, V.field c * V.field c.opposite = 1
def PartialBlockAverageReversalInverse : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j : ℕ, j < K → ∀ ℬ : Set (BondAtLevel L m K j), IsReversalClosed ℬ →
    (∀ U : BondAtLevel L m K j → ComplexMatrix2, IsGaugeField compactGaugeGroup ℬ U →
      (realPartialBlockAverage (Averaging.smoothingRadius L)
          (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K j)) :
        PartialGaugeField L m (levelDepth K (j + 1))).IsReversalInverse) ∧
    ∀ U : BondAtLevel L m K j → ComplexMatrix2, IsGaugeField complexGaugeGroup ℬ U →
      (complexPartialBlockAverage (⟨ℬ, U⟩ : PartialGaugeField L m (levelDepth K j)) :
        PartialGaugeField L m (levelDepth K (j + 1))).IsReversalInverse
end YangMills.Construction.PeriodicLattice
end
