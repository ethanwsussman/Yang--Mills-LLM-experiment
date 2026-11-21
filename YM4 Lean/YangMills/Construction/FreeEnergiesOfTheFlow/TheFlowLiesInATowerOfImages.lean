import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses
structure IsImageTower (Tb : ParameterAssignment) (y : ℝ) (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k : ℕ) : Prop
    extends ResponseInTheExpansion.IsTowerAtParameters Tb y T β k where
  siteDensities_eq : ∀ j < k, T.siteDensities (T.stage j).toStepSetup = (T.stage j).toStepSetup.stateDensity Tb.lam
  densities_eq : ∀ j < k, T.densities j = (T.stage j).toStepSetup.renormalizedDensity Tb.lam
def flowInImageTowerStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y =>
    ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β j).1) →
      ∃ T : StageTower (Tb.stepParameters y), IsImageTower Tb y T β k ∧ T.MarksMeasurable
end YangMills.Construction.FreeEnergies
end
