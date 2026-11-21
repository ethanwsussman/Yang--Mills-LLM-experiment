import YangMills.Construction.CellOfTheFlow.MajorantOfAState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields RenormalizationStepParameters StepSettings WeightedResponses BlockAverages
def majorantExpMomentStatement : Prop :=
  HoldsAtAdmissibleParametersWithConstants fun C s₁ Tb y => ∃ C₁ C₂ : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β s₀ : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k → 0 ≤ s₀ → s₀ ≤ C * (clusterRange β : ℝ) ^ 4 →
    PaysMajorant Tb y T s₀ s₁ k →
    ∀ (e : ℕ), (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ e →
      ∫⁻ u, ENNReal.ofReal (Real.exp (hullMajorantSum T s₀ s₁ k (2 * (Tb.stepParameters y).side ^ e) u))
          ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) ≤
        ENNReal.ofReal (Real.exp ((C₁ + C₂ * Real.log (T.stage k).coupling) *
          (2 * ((Tb.stepParameters y).side : ℝ) ^ e) ^ 4))
end YangMills.Construction.CellWindows
end
