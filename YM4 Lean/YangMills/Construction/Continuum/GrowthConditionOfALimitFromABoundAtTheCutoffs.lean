import YangMills.Construction.Continuum.GrowthConditionFromABoundOnSeparatedTuples
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitGrowthFromCutoffBound
variable {s : Conventions.StandingParameters}
def restrictToTestTuples (S : AmbientPoints.TupleMapFamily s .euclidean) :
    SeparatedBound.CorrelationFamily :=
  fun n hn X => S n hn ⟨X.1, (AmbientPoints.mem_separatedTuples_r4_iff X.1).2 X.2⟩
end YangMills.Construction.LimitGrowthFromCutoffBound
end
