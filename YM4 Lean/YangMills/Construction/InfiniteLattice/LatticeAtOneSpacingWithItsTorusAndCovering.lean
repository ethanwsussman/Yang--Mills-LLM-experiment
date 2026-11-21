import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace FixedSpacing
open InfiniteLattice
section LinkSets
variable {a : ℝ}
def IsLinkSet (S : Set (InfiniteLattice.Link a)) : Prop :=
  S ⊆ InfiniteLattice.positiveLinkSet a
def FactorsThroughFinite (S : Set (InfiniteLattice.Link a))
    (F : InfiniteLattice.GaugeField a → ℂ) : Prop :=
  S.Finite ∧ IsLinkSet S ∧
    ∃ φ : InfiniteLattice.LinkVariables S → ℂ, Continuous φ ∧
      ∀ U, F U = φ (InfiniteLattice.restrictField U S)
def finiteLinkFunctions (a : ℝ) : Set (InfiniteLattice.GaugeField a → ℂ) :=
  {F | ∃ S : Set (InfiniteLattice.Link a), FactorsThroughFinite S F}
def closedCube (r : ℝ) : Set InfiniteLattice.AmbientSpace :=
  {x | GibbsAtFixedSpacing.linfNorm x ≤ r}
abbrev observableAlgebra (a : ℝ) (O : Set InfiniteLattice.AmbientSpace) :
    Set (InfiniteLattice.GaugeField a → ℂ) :=
  InfiniteLattice.boundedRegionObservables a O
end LinkSets
structure Setup where
  L : ℕ
  admissible : Conventions.IsAdmissibleBlockingFactor L
  level : ℕ
  m : ℕ+
  β : ℝ
  β_pos : 0 < β
namespace Setup
variable (S : Setup)
abbrev mesh : ℝ := PeriodicLattice.meshSize S.L (S.level : ℤ)
abbrev side : ℝ := PeriodicLattice.torusSide S.L S.m
abbrev Torus : Type := PeriodicLattice.FourTorus S.L S.m
abbrev latticeSites : AddSubgroup InfiniteLattice.AmbientSpace :=
  InfiniteLattice.latticeSubgroup S.mesh
abbrev links : Set (InfiniteLattice.Link S.mesh) := InfiniteLattice.positiveLinkSet S.mesh
abbrev Fields : Type := InfiniteLattice.GaugeField S.mesh
abbrev torusSites : AddSubgroup S.Torus := PeriodicLattice.sublattice S.L S.m (S.level : ℤ)
abbrev TorusLink : Type := PeriodicLattice.Bond S.L S.m (S.level : ℤ)
abbrev TorusFace : Type := PeriodicLattice.Plaquette S.L S.m (S.level : ℤ)
def positiveTorusLinks : Set S.TorusLink := {b | b.IsPositivelyOriented}
abbrev TorusFields : Type := PeriodicLattice.CompactGaugeField S.L S.m (S.level : ℤ)
abbrev haarMeasure : Measure S.TorusFields :=
  PeriodicLattice.gaugeFieldMeasure S.L S.m (S.level : ℤ)
def faceEnergy (P : S.TorusFace) (U : S.TorusFields) : ℝ :=
  PeriodicLattice.plaquetteCost U.1 P
def wilsonEnergy (U : S.TorusFields) : ℝ := PeriodicLattice.wilsonAction U.1
def partitionFunction : ℝ := ∫ U, Real.exp (-S.β * S.wilsonEnergy U) ∂S.haarMeasure
def gibbs : Measure S.TorusFields :=
  (ENNReal.ofReal S.partitionFunction)⁻¹ •
    S.haarMeasure.withDensity fun U => ENNReal.ofReal (Real.exp (-S.β * S.wilsonEnergy U))
def smeared (h : S.Torus → ℝ) (U : S.TorusFields) : ℝ :=
  PeriodicLattice.smearedObservable h U.1
def cumulant {n : ℕ} (X : Fin n → S.TorusFields → ℝ) : ℂ :=
  Cumulants.mixedCumulant S.gibbs X
abbrev proj : InfiniteLattice.AmbientSpace → S.Torus := CutoffLattice.torusCover S.L S.m
def addVec (y : S.Torus) (v : InfiniteLattice.AmbientSpace) : S.Torus :=
  CutoffLattice.addVec S.L S.m S.level y v
def projLink (b : InfiniteLattice.Link S.mesh) : S.TorusLink :=
  InfiniteLattice.projectLink S.L S.m (S.level : ℤ) b
def projFace (p : InfiniteLattice.ElementaryPlaquette S.mesh) : S.TorusFace :=
  CutoffLattice.projectFace S.L S.m S.level p
end Setup
end FixedSpacing
end YangMills.Construction
