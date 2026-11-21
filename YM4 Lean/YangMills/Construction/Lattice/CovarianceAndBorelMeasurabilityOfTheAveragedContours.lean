import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Measurability.BorelKernelsAndParameterSetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K j : ℕ}
def gaugeFieldOfGroupValues (P : SymmetricBondSet L m K j)
    (v : PositiveBondsOf P → Matrices.ComplexMatrix2.specialUnitary) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  complexGaugeFieldOfValues P.bonds fun b =>
    ⟨(v b : Matrices.ComplexMatrix2), (Matrix.mem_specialUnitaryGroup_iff.mp (v b).2).2⟩
def GaugeFieldsArePowerOfGroup (P : SymmetricBondSet L m K j) : Prop :=
  Finite (PositiveBondsOf P) ∧
  (∀ v : PositiveBondsOf P → Matrices.ComplexMatrix2.specialUnitary,
    IsGaugeField compactGaugeGroup P.bonds (gaugeFieldOfGroupValues P v) ∧
      ∀ b : PositiveBondsOf P, gaugeFieldOfGroupValues P v b.1 = (v b : Matrices.ComplexMatrix2)) ∧
  ∀ U : BondAtLevel L m K j → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup P.bonds U →
    ∃ v : PositiveBondsOf P → Matrices.ComplexMatrix2.specialUnitary,
      ∀ b ∈ P.bonds, gaugeFieldOfGroupValues P v b = U b
def MeanContourCovarianceStatement : Prop :=
  ∀ L m K : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ j : ℕ, j < K →
  ∀ (y : SiteAtLevel L m K (j + 1)) (x : SiteAtLevel L m K j), x ∈ sitesInBlock (levelDepth K j) y →
    let P : SymmetricBondSet L m K j := bondsWithin (sitesInBlock (levelDepth K j) y)
    (∀ γ ∈ contourSet y x, ∀ b ∈ γ, b ∈ P.bonds) ∧
    GaugeFieldsArePowerOfGroup P ∧
    (∀ U : BondAtLevel L m K j → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup P.bonds U →
      ∀ g : SiteAtLevel L m K j → Matrices.ComplexMatrix2,
        (∀ z ∈ sitesInBlock (levelDepth K j) y, g z ∈ compactGaugeGroup) →
        (HasContourMean (gaugeTransform g U) y x ↔ HasContourMean U y x) ∧
        (HasContourMean U y x →
          meanContourHolonomy (gaugeTransform g U) y x =
            g (y.toSublattice (levelDepth K j)) * meanContourHolonomy U y x * (g x)⁻¹)) ∧
    MeasurableSet {v : PositiveBondsOf P → Matrices.ComplexMatrix2.specialUnitary |
      HasContourMean (gaugeFieldOfGroupValues P v) y x} ∧
    ∃ f : {v : PositiveBondsOf P → Matrices.ComplexMatrix2.specialUnitary //
        HasContourMean (gaugeFieldOfGroupValues P v) y x} → Matrices.ComplexMatrix2.specialUnitary,
      BorelKernels.IsBorelMeasurable f ∧
        ∀ v, (f v : Matrices.ComplexMatrix2) = meanContourHolonomy (gaugeFieldOfGroupValues P v.1) y x
end YangMills.Construction.PeriodicLattice
