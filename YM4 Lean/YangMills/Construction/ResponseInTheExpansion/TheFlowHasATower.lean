import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.ColdStepAtMirrorFrames
def TowerAlongFlowStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y =>
      (Tb.stepParameters y).Admissible ∧ 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side ∧
      ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k + 1, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β j).1) →
        ∃ T : StageTower (Tb.stepParameters y), IsTowerAtParameters Tb y T β k ∧
          IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn ∧ T.MarksMeasurable
end YangMills.Construction.ResponseInTheExpansion
end
