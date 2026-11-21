import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
open Classical
def localEventLikelyStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∃ c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N] (n : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
    N = 2 * (Tb.stepParameters y).side ^ e → IsLocalChainAbove Tb y T β k N n x₀ →
    MeasureTheory.Measure.real (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
      {u | ¬ IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ≤
      Real.exp (-(c * (couplingFlow (Tb.stepParameters y) β k).1))
end YangMills.Construction.ResponseInTheExpansion
end
