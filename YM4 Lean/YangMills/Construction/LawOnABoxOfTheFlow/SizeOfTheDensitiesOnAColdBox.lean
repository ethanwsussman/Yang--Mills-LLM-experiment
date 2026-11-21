import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
open WeightedResponses ResponseInTheExpansion BoxGaussian TorusFields TorusLumps RenormalizationStepParameters
def coldBoxDensitySumStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₁ : ℝ, ∃ C xs : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (o : TorusSite n) (x : ℝ) (R : ℕ),
      IsBoxDatum Tb y T β κ₀ xs k n → x = flowCoupling (Tb.stepParameters y) β k → R = boxRadius κ₀ x →
      ∀ W : TorusField n, (∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature W p.1 p.2.1 p.2.2 ≤ C₁ * (R : ℝ) ^ 2 * boxScale x) →
        mirrorSum (T.stage k).density o R abs W ≤ C * (Tb.stepParameters y).E * (R : ℝ) ^ 8 * boxScale x ^ 2
end YangMills.Construction.BoxEvents
end
