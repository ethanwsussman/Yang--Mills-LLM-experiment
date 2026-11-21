import YangMills.Construction.InfiniteLattice.CountableDenseSetOfContinuousLocalObservables
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilityOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice
namespace LatticePhases
def conditionalGibbsLocus (D : Setup)
    (κ : GaugeField D.mesh → ProbMeasure (GaugeField D.mesh)) : Set (GaugeField D.mesh) :=
  {U | ∀ F ∈ D.denseLocalSet,
    (∀ W : OrientedLinkSet D.mesh, (κ U).eval (W.heatBath D.β F) = (κ U).eval F) ∧
      ∀ v : LatticePoint D.mesh, (κ U).eval ((shift v).actOn F) = (κ U).eval F}
def AlmostEveryConditionalIsPeriodicGibbs : Prop :=
  ∀ (D : Setup) (ν : periodicGibbsSet D.L D.K D.β)
    (κ : GaugeField D.mesh → ProbMeasure (GaugeField D.mesh)),
    IsInvariantConditionalFamily D ν κ →
      MeasurableSet[shiftInvariantSigma D.mesh] (conditionalGibbsLocus D κ) ∧
        ν.1 (conditionalGibbsLocus D κ) = 1 ∧
          ∀ U ∈ conditionalGibbsLocus D κ,
            (κ U).toMeasure ∈ periodicGibbsSet D.L D.K D.β
end LatticePhases
end YangMills.Construction
end
