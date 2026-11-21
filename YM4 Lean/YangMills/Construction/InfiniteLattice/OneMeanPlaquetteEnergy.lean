import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def MeanFaceEnergyIsUniform : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (β : ℝ), 0 < β →
    ∀ ν : MeasureTheory.Measure (GaugeField a), IsPeriodicGibbs β ν →
      ∀ p p' : ElementaryPlaquette a,
        stateEval ν (fun U : GaugeField a => faceEnergy U p) =
          stateEval ν (fun U : GaugeField a => faceEnergy U p')
end YangMills.Construction.InfiniteLattice
end
