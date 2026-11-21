import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def scoreExpMeanBoundStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ C : ℝ, 0 ≤ C ∧ ∃ y₀ : ℝ,
    ∀ (y : ℝ) (R : StepSettings.StepSetup) (s : R.labels.Ω → ℝ) (n : ℕ) [NeZero n],
    y₀ ≤ y → R.params = T.stepParameters y → y ≤ R.coupling → R.HasExpansions →
    WeightedResponses.PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s →
    TorusLumps.IsBlockTorusSide R.params n →
    ResponseInTheExpansion.stateLIntegral R n (fun _ Y ω => Real.exp (∑ z : Y, s (ω z))) ≤
      ENNReal.ofReal (Real.exp (C * (1 + Real.log R.coupling) * (n : ℝ) ^ 4)) *
        ResponseInTheExpansion.stateLIntegral R n fun _ _ _ => 1
end YangMills.Construction.SmallTorusCopies
end
