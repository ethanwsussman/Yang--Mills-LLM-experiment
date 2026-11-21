import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def windowTowerExistsStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y =>
    (Tb.stepParameters y).Admissible ∧
    11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side ∧
    ∃ x₀ : ℝ, ∀ (β : ℝ) (k : ℕ), x₀ ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 →
      (∀ j ≤ k + 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1,
        (Tb.stepParameters y).y₁ ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1) →
      ∃ T : WeightedResponses.StageTower (Tb.stepParameters y),
        IsTowerAtParameters Tb y T β
          (k + 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1) ∧
        ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn ∧
        T.MarksMeasurable
end YangMills.Construction.ResponseInTheExpansion
end
