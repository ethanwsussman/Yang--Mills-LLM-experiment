import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import YangMills.Construction.RunningCouplingSlope.ActionsNearTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def NondegenerateAcrossFrames : Prop :=
  ∀ (F G : BlockAverages.BlockFrame) (K : ℕ) (a : ℝ) [Fintype (F.Site K)] [Fintype (G.Site K)],
    ColdStepAtMirrorFrames.SharePeriods F G K →
    IsNondegenerateAtTrivial (F := G) (k := K)
      (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells G) K) →
    IsNondegenerateAtTrivial (F := F) (k := K)
      (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells F) K)
end YangMills.Construction.RunningCouplingSlope
end
