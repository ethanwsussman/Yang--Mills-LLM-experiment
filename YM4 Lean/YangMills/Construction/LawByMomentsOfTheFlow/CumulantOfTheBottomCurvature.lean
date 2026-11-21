import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def baseCurvatureCumulantStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (a : ℝ) (K n : ℕ) [NeZero n] (k : ℕ) [NeZero k], 2 ≤ k →
    ∀ (h : Fin k → WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L K n))
    (μ : Measure (LevelChain L K n)), IsProbabilityMeasure μ →
    (∀ co : ChainNoise L K n → ℝ,
      μ.map (noisePairing K n co) = gaussianReal 0 (noiseVariance a K n co).toNNReal) →
    jointCumulant μ (fun i X => baseObservable (h i) X) =
      3 * (if k = 2 then 1 / 2 else 1) * ∑ σ ∈ CyclicFormula.unorientedCyclicOrders k,
        ∑ p : Fin k → WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide L K n),
        (∏ i, h i (p i).1) * ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1)))
end YangMills.Construction.MomentLaw
end
