import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def SchemeValuesInGaugeGroup : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K n : ℕ, 0 < m → n < K → ∀ s : AveragingScheme,
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      ∀ W : BondAtLevel L m K n → YangMills.Construction.Matrices.ComplexMatrix2,
      IsSchemeAverageDefined s W c → IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W →
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomy s W y x ∈ compactGaugeGroup) ∧
      (∀ x ∈ sitesInBlock (levelDepth K n) c.source, localDefect s W c x ∈ compactGaugeGroup) ∧
      (∃ Y ∈ YangMills.Construction.Matrices.ComplexMatrix2.hermitianTraceless,
        (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          YangMills.Construction.Matrices.ComplexMatrix2.logSeries (localDefect s W c x)) =
          Complex.I • Y) ∧
      schemeBlockAverage s W c ∈ compactGaugeGroup
end YangMills.Construction.PeriodicLattice
