import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjects
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def StepObjectsChartInvariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ r : ℝ, IsAdmissiblePolydiscRadius L r →
    ∀ m K n m' K' n' : ℕ, 0 < m → n < K → 0 < m' → n' < K' → ∀ (s : AveragingScheme) (μ : Fin 4)
      (c : BondAtLevel L m K (n + 1)) (c' : BondAtLevel L m' K' (n' + 1))
      (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n'),
      c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
      c'.target - c'.source = unitStep L m' (levelDepth K' (n' + 1)) μ →
      IsDoubleBlockChart c c' f →
      ∀ (a₀ a : LieBondField (doubleBlockSymmetricSet c))
        (a₀' a' : LieBondField (doubleBlockSymmetricSet c')),
        supOperatorNorm a₀ < r → supOperatorNorm a < r →
        FieldsAgreeInChart f a₀ a₀' → FieldsAgreeInChart f a a' →
        StepValuesAgreeInChart s c c' f a₀ a a₀' a'
end YangMills.Construction.PeriodicLattice
