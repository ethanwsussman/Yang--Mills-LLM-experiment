import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def stepScoreMeasurableAboveStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ (v j : ℕ) (i : Fin Λ.k), v ≤ j → IsMeasurableAbove S v (centredStepScore j i S)
end YangMills.Construction.MomentLaw
end
