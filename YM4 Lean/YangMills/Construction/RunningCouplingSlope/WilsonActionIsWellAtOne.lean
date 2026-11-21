import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import YangMills.Construction.RunningCouplingSlope.ActionsNearTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def WilsonActionNondegenerate : Prop :=
  ∀ (a : ℝ) (L n : ℕ) [Fintype ((TorusFields.torusFrame L 0 n).Site 0)], Odd L → 2 ≤ n →
    IsNondegenerateAtTrivial (F := TorusFields.torusFrame L 0 n) (k := 0)
      (BlockAverages.minimalAction a
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L 0 n)) 0)
end YangMills.Construction.RunningCouplingSlope
end
