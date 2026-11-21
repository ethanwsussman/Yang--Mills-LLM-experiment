import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
def CentredSchemeAtSmallCurvature.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
    ∀ W : BondAtLevel L m K n → ComplexMatrix2,
      IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W →
      doubleBlockCurvature W c < Averaging.smoothingRadius L →
      IsSchemeAverageDefined .centred W c ∧
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y, HasContourMean W y x) ∧
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y,
          contourHolonomy .centred W y x = meanContourHolonomy W y x) ∧
      IsRegularAveragingCase (Averaging.smoothingRadius L) W c ∧
      schemeBlockAverage .centred W c = blockAverage (Averaging.smoothingRadius L) W c
end PeriodicLattice
end YangMills.Construction
