import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def gaussianChainCoordinatesStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ u d : ℕ, u + d = S.data.windowLevel →
    (∀ (X : ColourForm (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)))
      (p : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))),
      curlNorm X p.1 ^ 2 ≤ C 0 * kineticForm Λ.stepParams.coupling Λ.stepParams.side u X) ∧
    ∀ μ : Measure (LevelChain Λ.stepParams.side (u + d) (S.data.period Λ.stepParams.side)),
    IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (u + d) (S.data.period Λ.stepParams.side)) μ →
    (∀ co : ChainNoise Λ.stepParams.side (u + d) (S.data.period Λ.stepParams.side) → ℝ,
      μ.map (noisePairing (u + d) (S.data.period Λ.stepParams.side) co) =
      gaussianReal 0 (noiseVariance Λ.stepParams.coupling (u + d) (S.data.period Λ.stepParams.side) co).toNNReal) ∧
    IsCanonicalGaussian (kineticForm Λ.stepParams.coupling Λ.stepParams.side u)
      (μ.map fun X => chainTop u (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))
        (chainDescend u d (S.data.period Λ.stepParams.side) X)) ∧
    ∀ p : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)),
      ∫⁻ X, ENNReal.ofReal (curlNorm (chainTop u (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))
        (chainDescend u d (S.data.period Λ.stepParams.side) X)) p.1 ^ 2) ∂μ ≤
        ENNReal.ofReal (C 0)
end YangMills.Construction.MomentLaw
end
