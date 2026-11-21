import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.WeightedWilsonActions
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure CutoffData where
  L : ℕ
  isAdmissible : Conventions.IsAdmissibleBlockingFactor L
  m : ℕ+
  cutoff : ℕ
namespace CutoffData
def atCutoff (s : Conventions.StandingParameters) : CutoffData :=
  ⟨s.L, s.isAdmissible, s.m, s.K⟩
variable (d : CutoffData)
abbrev Torus : Type := PeriodicLattice.FourTorus d.L d.m
abbrev Bond : Type := PeriodicLattice.Bond d.L d.m (d.cutoff : ℤ)
abbrev PosBond : Type := PeriodicLattice.PositivelyOrientedBond d.L d.m (d.cutoff : ℤ)
abbrev Plaquette : Type := PeriodicLattice.Plaquette d.L d.m (d.cutoff : ℤ)
def GaugeField : Type :=
  {U : d.Bond → Matrices.ComplexMatrix2 // U ∈ compactGaugeFields d.L d.m (d.cutoff : ℤ)}
instance : CoeFun d.GaugeField fun _ => d.Bond → Matrices.ComplexMatrix2 := ⟨Subtype.val⟩
def restrictPositive (U : d.GaugeField) :
    d.PosBond → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => ⟨U b.1, U.2.1 b.1 (mem_univ b.1)⟩
instance : TopologicalSpace d.GaugeField := .induced d.restrictPositive inferInstance
instance : MeasurableSpace d.GaugeField := borel d.GaugeField
instance : BorelSpace d.GaugeField := ⟨rfl⟩
abbrev haar : Measure (d.Bond → Matrices.ComplexMatrix2) :=
  productHaarMeasure d.L d.m (d.cutoff : ℤ)
def haarOnGaugeFields : Measure d.GaugeField :=
  Measure.comap (fun U : d.GaugeField => U.1) d.haar
abbrev plaquetteTerm (U : d.Bond → Matrices.ComplexMatrix2) (p : d.Plaquette) : ℂ :=
  plaquetteEnergy U p
abbrev weightedByPlaquettes (c : d.Plaquette → ℂ) (U : d.Bond → Matrices.ComplexMatrix2) : ℂ :=
  plaquetteWeightedEnergy c U
abbrev weightedByTorus (c : d.Torus → ℂ) (U : d.Bond → Matrices.ComplexMatrix2) : ℂ :=
  barycenterWeightedEnergy c U
end CutoffData
end YangMills.Construction.PeriodicLattice
