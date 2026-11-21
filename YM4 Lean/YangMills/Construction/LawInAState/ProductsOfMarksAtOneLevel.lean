import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses BoxResponses
open InfiniteLattice (AmbientSpace)
structure IsSeparatedBumpFamily (d vt : ℝ) {p : ℕ} (φ : Fin p → AmbientSpace → ℝ) : Prop where
  nonneg : ∀ i x, 0 ≤ φ i x
  le_one : ∀ i x, φ i x ≤ 1
  lipschitz : ∀ i x x', |φ i x - φ i x'| ≤ TorusMetric.euclidNormVec (x - x') / (vt * d)
  support_in_ball : ∀ i, ∃ c, tsupport (φ i) ⊆ TestFunctions.closedBallR4 c d
  separated : ∀ i j, i ≠ j → ∀ x ∈ tsupport (φ i), ∀ x' ∈ tsupport (φ j), ∀ z : Fin 4 → ℤ,
    d ≤ TorusMetric.euclidNormVec (fun a => x a - x' a + 2 * (z a : ℝ))
def centeredProductsAtLevelStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (α : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)), IsStateChain Tb y Kr Xi d K β α T →
    ∀ (p : ℕ) (φ : Fin p → AmbientSpace → ℝ), p ≤ 32 → IsSeparatedBumpFamily d vt φ → ∀ I : Finset (Fin p),
      |∫ U, ∏ i ∈ I, (smearedObservable (Tb.stepParameters y).side K (φ i) U -
              unitTorusMean (Tb.stepParameters y).side K β (φ i)) ∂unitTorusMeasure (Tb.stepParameters y).side K β -
          ∫ u, ∏ i ∈ I, centeredBoxResponse T β α K (separationLevel (Tb.stepParameters y) β K d) (φ i) u
            ∂stageLaw T β K (separationLevel (Tb.stepParameters y) β K d)| ≤
        markError (Tb.stepParameters y) C (couplingAtSeparation (Tb.stepParameters y) β K d)
end YangMills.Construction.StateLaws
end
