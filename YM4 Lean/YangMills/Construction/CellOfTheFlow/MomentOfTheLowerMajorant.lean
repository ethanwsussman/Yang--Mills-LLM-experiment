import YangMills.Construction.CellOfTheFlow.MajorantOfAState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters
def lowerScoreMomentStatement : Prop :=
  HoldsAtAdmissibleParametersWithConstants fun C s₁ Tb y => ∃ C₁ C₂ : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β s₀ : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k → 0 ≤ s₀ → s₀ ≤ C * (clusterRange β : ℝ) ^ 4 →
    PaysMajorant Tb y T (16 * s₀) (16 * s₁) k →
    ∀ (e a : ℕ) (G : CellGrid) (κ : Fin 4 → ℤ),
      G.side = baseCellSide (Tb.stepParameters y).side (stageRange T k) * (Tb.stepParameters y).side ^ a →
      2 * G.side ≤ 2 * (Tb.stepParameters y).side ^ e → κ ∈ G.indices (2 * (Tb.stepParameters y).side ^ e) →
      ∫⁻ u, ENNReal.ofReal (Real.exp (lowerScoreSum T k s₀ s₁ k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ)))
          ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) ≤
        ENNReal.ofReal (Real.exp ((C₁ + C₂ * Real.log (T.stage k).coupling) * (G.side : ℝ) ^ 4)) ∧
      ∀ q : ℕ, 1 ≤ q →
        ∫⁻ u, ENNReal.ofReal (lowerScoreSum T k s₀ s₁ k _ u (G.cell (2 * (Tb.stepParameters y).side ^ e) κ) ^ q)
            ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) ≤
          ENNReal.ofReal (((q : ℝ) + (C₁ + C₂ * Real.log (T.stage k).coupling) * (G.side : ℝ) ^ 4) ^ q)
end YangMills.Construction.CellWindows
end
