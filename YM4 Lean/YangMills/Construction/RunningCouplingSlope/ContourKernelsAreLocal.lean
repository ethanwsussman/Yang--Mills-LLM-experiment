import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open Conventions TorusFields TorusLumps FlatLinearization SlopeCoefficient
def ContourWeightLocality : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∃ C : ℝ, 0 < C ∧
    (∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L],
      (∀ (ξ : RealOneForm (n * L)) (c : TorusBond n), contourAverage L ξ c = ∑ b, contourWeight L c b * ξ b) ∧
      ∀ (c : TorusBond n) (b : TorusBond (n * L)), |contourWeight L c b| ≤ C ∧
        (5 * L < supDist b.1 (blockCentreSite L c.1) → contourWeight L c b = 0)) ∧
    (∀ c b : LatticeBond, |latticeContourWeight L c b| ≤ C ∧
      ((5 * L : ℕ) < offsetNorm (b.1 - blockCentreOnLattice L c.1) → latticeContourWeight L c b = 0)) ∧
    (∀ c b : LatticeBond, ∀ᶠ n : ℕ in Filter.atTop,
      contourWeight L (bondFrom 0 c : TorusBond n) (bondFrom 0 b : TorusBond (n * L)) = latticeContourWeight L c b) ∧
    ∀ b : LatticeBond, ∀ᶠ n : ℕ in Filter.atTop,
      (IsBlockTreeBond L (bondFrom 0 b : TorusBond (n * L)) ↔ IsLatticeTreeBond L b)
end YangMills.Construction.RunningCouplingSlope
end
