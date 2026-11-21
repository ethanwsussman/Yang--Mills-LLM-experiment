import YangMills.Construction.InfiniteLattice.PeriodicExtensionsStatesAndTorusFunctionalsAtOneSpacing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice
namespace FixedSpacing
def LiftedGibbsIsInvariantProbability : Prop :=
  ∀ D : Setup, IsProbabilityMeasure D.liftedGibbs ∧ IsShiftInvariant D.liftedGibbs
end FixedSpacing
end YangMills.Construction
