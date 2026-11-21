import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SchemesOfTheOneStepToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
structure IsGaugeCovariantAt (s : AveragingScheme) (h : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2) (c : BondAtLevel L m K (n + 1)) : Prop where
  contour : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined s W y x →
      IsContourHolonomyDefined s (gaugeTransform h W) y x ∧
        contourHolonomy s (gaugeTransform h W) y x =
          h (schemeBaseSite s (levelDepth K n) y) * contourHolonomy s W y x * (h x)⁻¹
  average : IsOneStepAverageFormed s W c →
    IsOneStepAverageFormed s (gaugeTransform h W) c ∧
      oneStepAverage s (gaugeTransform h W) c =
        h (schemeBaseSite s (levelDepth K n) c.source) * oneStepAverage s W c *
          (h (schemeBaseSite s (levelDepth K n) c.target))⁻¹
def GaugeCovarianceStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ s : AveragingScheme,
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      ∀ (h : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
        (W : BondAtLevel L m K n → Matrices.ComplexMatrix2),
        (∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c → h x ∈ compactGaugeGroup) →
        IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W →
        IsGaugeCovariantAt s h W c
end YangMills.Construction.PeriodicLattice
