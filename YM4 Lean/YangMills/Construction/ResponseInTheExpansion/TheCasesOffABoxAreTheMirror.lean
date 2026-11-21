import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import YangMills.Construction.ResponseInTheExpansion.MirrorLawOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open Classical in
def casesAwayFromBall (R : StepSettings.StepSetup) {n : ℕ} [NeZero n] (V : TorusFields.TorusField n)
    (Q : Finset (TorusFields.TorusSite n)) (Z : Finset (TorusFields.TorusBond (n * R.params.side)))
    (F : (↥Z × Fin 3 → ℝ) → ℝ) : WeightedResponses.CaseFunction R n :=
  fun W Yt _ bad _ => if FreeCoresAvoid R Yt bad (StepSettings.hotCoreSites R V) Q then
    F (imaginaryComponentsOn Z (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V W)) else 0
def casesAwayFromBallReflectStatement : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.ColdStepHolds → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.IsWellPosed →
      R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n m : ℕ) [NeZero n] [NeZero (4 * m)] (V : TorusFields.TorusField n) (q : StepSettings.CoarseState R n)
        (o : TorusFields.TorusSite n),
        TorusLumps.IsBlockTorusSide R.params n → TorusLumps.IsHullState R.params R.nextRange V q.1 →
        (∀ X ∈ TorusLumps.chainComponents R.nextRange q.1, StepSettings.coarseFactor V q X ≠ 0) →
        2 ^ 12 * R.range ≤ m → 8 * m ≤ n → Disjoint q.1 (supBall o m) →
        ∀ (Z : Finset (TorusFields.TorusBond (n * R.params.side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) (B : ℝ),
          Z ⊆ MarkedIntegrals.chartBondsInBlocks R.params.side (supBall o ((m : ℝ) / 8)) → Measurable F →
          (∀ v, |F v| ≤ B) →
          |WeightedResponses.caseMean R (StepSettings.hotCoreSites R V) V q (casesAwayFromBall R V (supBall o m) Z F) -
            reflectedStepMean R m o V
              (fun k => F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o k)))| ≤
          2 * B * Real.exp (-(T.rt * ((m - R.frameReach - 1 : ℕ) : ℝ) / 2 ^ 3)) +
            2 * B * (blocksNearFreeCores R.params.side R.range (supBall o m)).card * Real.exp (-(7 * T.gasRate * R.coupling))
end YangMills.Construction.ResponseInTheExpansion
end
