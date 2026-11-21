import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SchemesOfTheOneStepToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def OneStepAverageIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
      ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
        IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W →
        IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W' →
        Set.EqOn W W' (bondsInDoubleBlock c) →
          (IsOneStepAverageFormed s W c ↔ IsOneStepAverageFormed s W' c) ∧
          (IsOneStepAverageFormed s W c →
            oneStepAverage s W c = oneStepAverage s W' c ∧
            oneStepAverage s W c.opposite = oneStepAverage s W' c.opposite)
end YangMills.Construction.PeriodicLattice
end
