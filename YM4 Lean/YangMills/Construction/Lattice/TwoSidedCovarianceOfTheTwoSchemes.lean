import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def SchemesGaugeCovariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ s : AveragingScheme,
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      ∀ (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
        (W : BondAtLevel L m K n → Matrices.ComplexMatrix2),
        (∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c →
          g x ∈ compactGaugeGroup) →
        IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W →
        (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
          ∀ x ∈ sitesInBlock (levelDepth K n) y,
            (IsContourHolonomyDefined s (gaugeTransform g W) y x ↔
              IsContourHolonomyDefined s W y x)) ∧
        (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
          ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined s W y x →
            contourHolonomy s (gaugeTransform g W) y x =
              g (schemeBaseSite s (levelDepth K n) y) * contourHolonomy s W y x * (g x)⁻¹) ∧
        (IsSchemeAverageDefined s (gaugeTransform g W) c ↔ IsSchemeAverageDefined s W c) ∧
        (IsSchemeAverageDefined s W c →
          schemeBlockAverage s (gaugeTransform g W) c =
            g (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s W c *
              (g (schemeBaseSite s (levelDepth K n) c.target))⁻¹) ∧
        (AreContourHolonomiesDefined s W c → ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
          localDefect s (gaugeTransform g W) c x =
            g (schemeBaseSite s (levelDepth K n) c.source) * localDefect s W c x *
              (g (schemeBaseSite s (levelDepth K n) c.source))⁻¹)
end YangMills.Construction.PeriodicLattice
