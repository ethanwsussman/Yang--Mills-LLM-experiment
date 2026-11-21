import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open Classical
def curvedFieldResponseStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y =>
    ∀ Kr : WeightedResponses.ResponseParameters, Kr.Admissible (Tb.stepParameters y) → ∃ C c x₀ : ℝ, 0 < c ∧
    ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ) (n : ℕ) [NeZero n],
      (∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β j) →
      x₀ ≤ ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k →
      ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr β k al → |al k| ≤ 2 →
      (Tb.stepParameters y).n₀ ≤ n →
      ∀ (z : TorusFields.TorusSite n)
        (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide (Tb.stepParameters y).side k n)),
        WeightedResponses.weightSup h ≤ 1 → WeightedResponses.weightLipschitz (Tb.stepParameters y).side k h ≤ 1 →
      ∃ κ : TorusFields.TorusPlaquette n → TorusFields.TorusPlaquette n → ℝ,
        (∀ p p', κ p p' = κ p' p) ∧
        (∀ p p', |κ p p'| ≤ C * Real.exp (-(c * max (TorusFields.supDist p.1 z : ℝ) (TorusFields.supDist p'.1 z : ℝ)))) ∧
        (∀ μ ν ρ τ : Fin 4, μ < ν → ρ < τ →
          |∑ p ∈ (TorusFields.plaquettesIn Finset.univ).filter (fun p : TorusFields.TorusPlaquette n => p.2 = (μ, ν)),
              ∑ p' ∈ (TorusFields.plaquettesIn Finset.univ).filter
                (fun p' : TorusFields.TorusPlaquette n => p'.2 = (ρ, τ)), κ p p' -
            (if (μ, ν) = (ρ, τ) then al k * WeightedResponses.blockMean (Tb.stepParameters y).side k n z h else 0)| ≤
              C * (WeightedResponses.weightLipschitz (Tb.stepParameters y).side k h + Real.exp (-(c * n)))) ∧
        ∀ (W : TorusFields.TorusField n) (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
          (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (ρ s t : ℝ),
          TorusFields.IsCold (Tb.stepParameters y).threshold W →
          1 ≤ ρ → 4 * ρ + 4 ≤ n → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
          (∀ b : TorusFields.TorusBond n, b.1 ∈ ResponseInTheExpansion.supBall z ρ → ‖(v b : Quaternion ℝ)‖ ≤ s ∧
            ‖(v b : Quaternion ℝ) -
              (LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : Quaternion ℝ)‖ ≤ s ^ 2) →
          (∀ x ∈ ResponseInTheExpansion.supBall z ρ, ∀ μ ν : Fin 4, TorusFields.curvature W x μ ν ≤ t) →
          (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall z ρ),
            ‖(ResponseInTheExpansion.lieFormCurl v p : Quaternion ℝ)‖ ≤ t) →
            |WeightedResponses.centeredResponse
                (ResponseInTheExpansion.coldResponseChain (Tb.stepParameters y) β
                  (ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β) al k) n z W h -
                (1 / 2) * ∑ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall z ρ),
                  ∑ p' ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall z ρ),
                  κ p p' * ∑ e : Fin 3, BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl v p) *
                    BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl v p')| ≤
              C * (t ^ 3 + t * s ^ 2 + Real.exp (-(c * ρ)))
end YangMills.Construction.StateLaws
end
