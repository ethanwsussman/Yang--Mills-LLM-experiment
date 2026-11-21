import YangMills.Construction.CellOfTheFlow.MajorantOfAState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields RenormalizationStepParameters WeightedResponses BlockAverages LumpContours
def majorantNearBoxMomentsStatement : Prop :=
  HoldsAtAdmissibleParametersWithConstants fun C s₁ Tb y => ∀ (R : ℝ) (p : ℕ), 1 ≤ R → 1 ≤ p → ∃ Cp : ℝ,
    (∀ (T : StageTower (Tb.stepParameters y)) (β s₀ : ℝ) (k : ℕ), IsTowerAtParametersMeasurable Tb y T β k → 0 ≤ s₀ →
      s₀ ≤ C * (clusterRange β : ℝ) ^ 4 → PaysMajorant Tb y T (16 * s₀) (16 * s₁) k →
      ∀ (e : ℕ), (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ e →
      ∀ y₀ : TorusSite (2 * (Tb.stepParameters y).side ^ e),
        ∫⁻ u, ENNReal.ofReal (majorantNearBox T s₀ s₁ k _ u y₀ R ^ p)
            ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) ≤
          ENNReal.ofReal (Cp * ((stageRange T k : ℝ) ^ 4 * Real.log (T.stage k).coupling) ^ p)) ∧
    ∀ Ξ : ℝ, ∃ CΞ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β s₀ : ℝ) (k : ℕ),
      IsTowerAtParametersMeasurable Tb y T β k →
      (T.stage k).coupling ≤ Ξ →
      0 ≤ s₀ → s₀ ≤ C * (clusterRange β : ℝ) ^ 4 → PaysMajorant Tb y T (16 * s₀) (16 * s₁) k →
      ∀ (e : ℕ), (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ e →
      ∀ y₀ : TorusSite (2 * (Tb.stepParameters y).side ^ e),
        ∫⁻ u, ENNReal.ofReal (majorantNearBox T s₀ s₁ k _ u y₀ R ^ p)
            ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) ≤
          ENNReal.ofReal CΞ
end YangMills.Construction.CellWindows
end
