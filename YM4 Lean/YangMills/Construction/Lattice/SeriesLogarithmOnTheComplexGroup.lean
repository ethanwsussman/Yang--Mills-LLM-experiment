import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Conventions Matrices
namespace PeriodicLattice
def LogSeriesInComplexGroupStatement : Prop :=
  (∀ X ∈ complexGaugeGroup, ComplexMatrix2.operatorNorm (X - 1) < 1 →
    ComplexMatrix2.fullTrace (ComplexMatrix2.logSeries X) = 0 ∧
      ComplexMatrix2.logSeries X ∈ complexLieAlgebra) ∧
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      (∀ W ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → ComplexMatrix2)),
        complexBlockAverage W c ∈ complexGaugeGroup) ∧
      ∀ (U : BondAtLevel L m K n → ComplexMatrix2) (a : LieBondField (doubleBlockSymmetricSet c)),
        IsGaugeField complexGaugeGroup (doubleBlockSymmetricSet c).bonds U →
          (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
            (∀ x ∈ sitesInBlock (levelDepth K n) y, StepLogDefinedAt .centred c a U y x →
              stepLog .centred c a U y x ∈ complexLieAlgebra) ∧
            (StepGaugeDefinedAt .centred c a U y →
              stepGauge .centred c a U y ∈ complexGaugeGroup)) ∧
          (StepVariableDefined .centred c a U → stepVariable .centred c a U ∈ complexLieAlgebra)
end PeriodicLattice
end YangMills.Construction
