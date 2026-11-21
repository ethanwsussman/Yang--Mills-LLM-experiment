import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def scoreIsometryInvariantStatement : Prop :=
  ∀ P : TorusLumps.StepParameters, P.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n], P.n₀ ≤ n →
    ∀ (g : TorusFields.TorusIsometry) (W W' : TorusFields.TorusField (n * P.side)) (V V' : TorusFields.TorusField n),
    (g.scaledLift P.side).Transports W W' → g.Transports V V' →
    ∃ τ : StepCosts.BaseChoice P.side n ≃ StepCosts.BaseChoice P.side n, ∀ b : StepCosts.BaseChoice P.side n,
      WeightedResponses.stepTransitionDensity P x W' (τ b) V' = WeightedResponses.stepTransitionDensity P x W b V ∧
      (b ∈ TorusLumps.baseChoices P (TorusLumps.fineLevelField P n W) → ∀ Y : TorusFields.TorusSite n,
        ResponseInTheExpansion.bondScoresAtSite P x W' V' (τ b) (g.mapSite Y) = ResponseInTheExpansion.bondScoresAtSite P x W V b Y)
end YangMills.Construction.SmallTorusCopies
end
