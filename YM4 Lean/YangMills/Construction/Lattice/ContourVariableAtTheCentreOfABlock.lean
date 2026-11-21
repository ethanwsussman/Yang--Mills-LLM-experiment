import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ContourHolonomyAtBlockCentre : Prop :=
  ∀ L m K n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → n < K →
    ∀ (y : SiteAtLevel L m K (n + 1)) (U : BondAtLevel L m K n → Matrices.ComplexMatrix2),
      IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) U →
      y.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) y ∧
        Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y (y.toSublattice (levelDepth K n))) <
          Averaging.centreOfMassDiameter ∧
        complexMeanContourHolonomy U y (y.toSublattice (levelDepth K n)) = 1
end YangMills.Construction.PeriodicLattice
end
