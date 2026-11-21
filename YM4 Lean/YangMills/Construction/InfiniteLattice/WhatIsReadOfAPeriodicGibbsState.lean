import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAsHyperplanesAndReflectionPositivityOfAState
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsConsequences
def SymmetriesAndConstantFaceMean : Prop :=
  ∀ a : ℝ, 0 < a → ∀ β : ℝ, 0 < β →
    ∀ ν : Measure (GaugeField a), IsPeriodicGibbs β ν →
      ((∀ r : latticeMotions a, IsSymmetricUnder ν (latticeMotionSymmetry r)) ∧
        ∀ P : LatticeMirror a,
          IsSymmetricUnder ν P.symmetry ∧ ReflectionPositiveAtMirror ν P) ∧
      ∀ p p' : ElementaryPlaquette a,
        stateEval ν (fun U : GaugeField a => faceEnergy U p) =
          stateEval ν (fun U : GaugeField a => faceEnergy U p')
end YangMills.Construction.InfiniteLattice.PeriodicGibbsConsequences
end
