import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
def gaugeDistFromOne (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : ℝ :=
  ⨆ x, Matrices.ComplexMatrix2.operatorNorm (g x - 1)
def gaugeBondTwist (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
    (b : BondAtLevel L m K n) : Matrices.ComplexMatrix2 :=
  (g b.source)⁻¹ * Matrices.ComplexMatrix2.conjugateBy (W b) (g b.target)
theorem inv_mem_specialUnitary {M : Matrices.ComplexMatrix2}
    (hM : M ∈ Matrices.ComplexMatrix2.specialUnitary) :
    M⁻¹ ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
def gaugeMaxAngle (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : ℝ :=
  ⨆ b, Matrices.ComplexMatrix2.rotationAngle (gaugeBondTwist W g b)
def covariantBlockAverage (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (f : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y,
    Matrices.ComplexMatrix2.conjugateBy (contourHolonomy AveragingScheme.centred W y x) (f x)
end PeriodicLattice
end YangMills.Construction
