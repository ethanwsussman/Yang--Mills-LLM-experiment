import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticePhases
open InfiniteLattice
def ergodicConditionalLocus (D : Setup)
    (κ : GaugeField D.mesh → ProbMeasure (GaugeField D.mesh)) : Set (GaugeField D.mesh) :=
  {U | U ∈ conditionalGibbsLocus D κ ∧
    ∀ A ∈ D.denseLocalSet, plateauVariance (κ U).toMeasure A = 0}
def AlmostEveryConditionalIsErgodic : Prop :=
  ∀ (D : Setup) (ν : periodicGibbsSet D.L D.K D.β)
    (κ : GaugeField D.mesh → ProbMeasure (GaugeField D.mesh)),
    IsInvariantConditionalFamily D ν κ →
      MeasurableSet[shiftInvariantSigma D.mesh] (ergodicConditionalLocus D κ) ∧
        ν.1 (ergodicConditionalLocus D κ) = 1 ∧
          ∀ U ∈ ergodicConditionalLocus D κ,
            (κ U).toMeasure ∈ extremalPhases D.L D.K D.β
end YangMills.Construction.LatticePhases
