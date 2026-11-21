import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice
open scoped Topology
noncomputable section
namespace YangMills.Construction.CutoffLinks.CutoffData
variable (d : CutoffData)
abbrev FieldProb : Type := GaugeFieldProbability d.spacing
def TendstoWeaklyComplex (ν : ℕ → d.FieldProb) (ν₀ : d.FieldProb) : Prop :=
  ∀ F : C(GaugeField d.spacing, ℂ),
    Tendsto (fun i => (ν i).expect F) atTop (𝓝 (ν₀.expect F))
abbrev periodizedWilsonMeasure : Measure (GaugeField d.spacing) :=
  CutoffLattice.periodizedMeasure d.L d.m d.K d.coupling
def torusWeakLimits : Set d.FieldProb :=
  {ν | ∃ (ℓ : ℕ → d.sideSet) (ρ : ℕ → d.FieldProb),
    Tendsto (fun i => (ℓ i : ℝ)) atTop atTop ∧
      (∀ i, (ρ i).1 = (d.withSide (ℓ i)).periodizedWilsonMeasure) ∧
      d.TendstoWeaklyComplex ρ ν}
end YangMills.Construction.CutoffLinks.CutoffData
end
