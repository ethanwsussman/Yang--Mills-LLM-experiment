import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjects
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
structure StepObjectsCovariance (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a a' : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : Prop where
  twisted_eq : ∀ b ∈ (doubleBlockSymmetricSet c).bonds,
    gaugeTransform g (twistedConfig c a W₀) b =
      twistedConfig c a' (gaugeTransform g W₀) b
  log_eq : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourRatioLogDefined s c a W₀ y x →
      IsContourRatioLogDefined s c a' (gaugeTransform g W₀) y x ∧
        stepLog s c a' (gaugeTransform g W₀) y x =
          Matrices.ComplexMatrix2.conjugateBy (g (schemeBaseSite s (levelDepth K n) y))
            (stepLog s c a W₀ y x)
  gauge_eq : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    IsStepGaugeDefined s c a W₀ y →
      IsStepGaugeDefined s c a' (gaugeTransform g W₀) y ∧
        stepGauge s c a' (gaugeTransform g W₀) y =
          g (schemeBaseSite s (levelDepth K n) y) * stepGauge s c a W₀ y *
            (g (schemeBaseSite s (levelDepth K n) y))⁻¹
  variable_eq : StepVariableDefined s c a W₀ →
    StepVariableDefined s c a' (gaugeTransform g W₀) ∧
      stepVariable s c a' (gaugeTransform g W₀) =
        Matrices.ComplexMatrix2.conjugateBy (g (schemeBaseSite s (levelDepth K n) c.source))
          (stepVariable s c a W₀)
  straightened_eq : (∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      IsContourHolonomyDefined s W₀ c.source x) →
    (∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      IsContourHolonomyDefined s (gaugeTransform g W₀) c.source x) ∧
      straightenedMap s c (gaugeTransform g W₀) a' =
        Matrices.ComplexMatrix2.conjugateBy (g (schemeBaseSite s (levelDepth K n) c.source))
          (straightenedMap s c W₀ a)
def StepObjectsGaugeCovariance : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)),
      c.IsPositivelyOriented →
      ∀ (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
        (a a' : LieBondField (doubleBlockSymmetricSet c))
        (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2),
        (∀ x, g x ∈ compactGaugeGroup) →
        (∀ b : PositiveBondsOf (doubleBlockSymmetricSet c),
          (a' b : Matrices.ComplexMatrix2) =
            Matrices.ComplexMatrix2.conjugateBy (g b.1.source) (a b : Matrices.ComplexMatrix2)) →
        IsGaugeField complexGaugeGroup (doubleBlockSymmetricSet c).bonds W₀ →
          StepObjectsCovariance s c a a' W₀ g
end YangMills.Construction.PeriodicLattice
