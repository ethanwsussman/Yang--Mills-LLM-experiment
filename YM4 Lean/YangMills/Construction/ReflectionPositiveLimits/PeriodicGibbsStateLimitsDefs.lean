import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.ReflectionPositivity.SeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicGibbsLimits
theorem get_mem_disjointSupportTuples (X : ReflectionPositivity.Tuple) :
    (fun i => X.1.get i) ∈ TestSpaces.disjointSupportTuples Set.univ X.1.length := by
  refine ⟨fun i => X.2.1 _ (List.get_mem _ _), fun i i' hne => ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact List.pairwise_iff_get.1 X.2.2 i i' h
  · exact (List.pairwise_iff_get.1 X.2.2 i' i h).symm
def toSepTuple (X : ReflectionPositivity.Tuple) : TestSpaces.SepTuple :=
  ⟨X.1.length, ⟨fun i => X.1.get i, get_mem_disjointSupportTuples X⟩⟩
end YangMills.Construction.PeriodicGibbsLimits
end
