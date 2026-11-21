import YangMills.Construction.Lattice.SoftGaugeFactor
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m : ℕ}
def axialShellSites (K j : ℕ) (Y : Set (SiteAtLevel L m K (j + 1))) :
    Set (SiteAtLevel L m K j) :=
  {z | (z : FourTorus L m) ∈ refinedBlockUnion 1 Y ∧ ∀ y ∈ Y, (z : FourTorus L m) ≠ y}
def axialShellCentre (K j : ℕ) (Y : Set (SiteAtLevel L m K (j + 1)))
    (z : SiteAtLevel L m K j) : SiteAtLevel L m K (j + 1) :=
  Classical.epsilon fun y => y ∈ Y ∧ z ∈ blockSitesExceptCenter K j y
def axialShellGauge (K j : ℕ) (Y : Set (SiteAtLevel L m K (j + 1)))
    (u : axialShellSites K j Y → ComplexMatrix2.specialUnitary) :
    SiteAtLevel L m K j → ComplexMatrix2 :=
  open Classical in
  fun z => if h : z ∈ axialShellSites K j Y then (u ⟨z, h⟩ : ComplexMatrix2) else 1
def axialShellSitesWithMean (K j : ℕ) (Y : Set (SiteAtLevel L m K (j + 1)))
    (V : BondAtLevel L m K j → ComplexMatrix2) : Set (SiteAtLevel L m K j) :=
  {z | z ∈ axialShellSites K j Y ∧ HasContourMean V (axialShellCentre K j Y z) z}
def axialShellLawFactor (t ε : ℝ) (K j : ℕ) (Y : Set (SiteAtLevel L m K (j + 1)))
    (V : BondAtLevel L m K j → ComplexMatrix2) (z : SiteAtLevel L m K j) :
    Measure ComplexMatrix2.specialUnitary :=
  open Classical in
  if z ∈ axialShellSitesWithMean K j Y V then
    ComplexMatrix2.haarProb.withDensity fun u => ENNReal.ofReal
      (softGaugeFixingWeight t ε
        (meanContourHolonomy V (axialShellCentre K j Y z) z * (u : ComplexMatrix2)⁻¹))
  else Measure.dirac 1
def axialShellLaw (t ε : ℝ) (K j : ℕ) [Finite (SiteAtLevel L m K j)]
    (Y : Set (SiteAtLevel L m K (j + 1))) (V : BondAtLevel L m K j → ComplexMatrix2) :
    Measure (axialShellSites K j Y → ComplexMatrix2.specialUnitary) :=
  letI : Fintype (axialShellSites K j Y) := Fintype.ofFinite _
  Measure.pi fun z => axialShellLawFactor t ε K j Y V z
end YangMills.Construction.PeriodicLattice
