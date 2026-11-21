import YangMills.Construction.LawOnABoxOfTheFlow.ChartOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BlockAverages BoxEvents
def boxGaussianLawStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 →
    ∃ (C C₀ xs : ℝ) (Cj : ℕ → ℝ) (xp : ℕ → ℝ),
      ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (o : TorusSite n) (x : ℝ) (R : ℕ),
        IsBoxDatum Tb y T β κ₀ xs k n → x = flowCoupling (Tb.stepParameters y) β k → R = boxRadius κ₀ x →
        ∃ c : BoxChart T k o R, c.IsMeasurable ∧
          (∀ p : ℕ, xp p ≤ x → 1 - x ^ (-(p : ℝ)) ≤ (markedSampleLaw T β k n).real c.event) ∧
          (∀ p ∈ c.orbitSet, Disjoint p.1.2.1 (supBall o (3 * R))) ∧
          c.IsInGauge C (boxScale x) (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) ∧
          c.HasLaw (markedSampleLaw T β k n) x (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2)
            (C * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) ∧
          c.HasCurl x C (boxScale x) (C * (R : ℝ) ^ (-(2 / 3 : ℝ)) * boxScale x) Cj ∧
          ∀ u : TorusPlaquette n → Fin 3 → ℝ, 0 ≤ curlQuadForm Tb.coupling Tb.side k o R u ∧
            curlQuadForm Tb.coupling Tb.side k o R u ≤
              (2 * Tb.coercivity)⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn (supBall o (2 * R)), u p e ^ 2
end YangMills.Construction.BoxGaussian
end
