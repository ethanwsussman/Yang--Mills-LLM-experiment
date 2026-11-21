import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjects
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def RealBondFieldStepStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ r : ℝ, IsAdmissiblePolydiscRadius L r →
    ∀ m K n : ℕ, 0 < m → n < K →
      ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
        ∀ W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2,
          IsGaugeField compactGaugeGroup (doubleBlockSymmetricSet c).bonds W₀ →
          doubleBlockCurvature W₀ c ≤ curvatureBound L r →
            ∀ a : LieBondField (doubleBlockSymmetricSet c), supOperatorNorm a < bondRadius L r →
              IsCompactValued a → StepQuantitiesReal s c W₀ a
end YangMills.Construction.PeriodicLattice
end
