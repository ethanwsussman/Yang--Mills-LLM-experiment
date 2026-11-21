import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open RenormalizationStepParameters StepSettings TorusFields TorusLumps StepCosts MomentLaw
def stepRemainderAtFrameFieldStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom (fun U => ColdRegimeEstimatesAt U ∧ blockSumExpectationNearValueAt U) →
      T.rt ≤ rt₀ T.toChainParameters → ∃ C₁ : ℝ, ∀ K : ResponseParameters, ∃ C₂ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
        ∀ (R : StepSetup) (A : ResponseSetup R),
        A.responseParams = K → OnStepParameters T y A → R.IsSymmetricWeight → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
          ∀ (Y : TorusSite n) (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (b b' : TorusBond n),
          |hessianAtIdentity (fun V : TorusField n => ∑ z ∈ sitesInBlocks R.params.side {Y},
              (blockMean R.params.side R.depth (n * R.params.side) z h - blockMean R.params.side (R.depth + 1) n Y h) *
                levelShare R.params.coupling R.params.side R.depth Finset.univ z
                  (ResponseInTheExpansion.coldFieldAboveFrames R V 0)) b b'| ≤
            C₁ * weightLipschitz R.params.side (R.depth + 1) h / R.params.weight (tripleDiam Y b b') ∧
          |hessianAtIdentity (responseRemainder A.coldStep n Y h) b b' -
              hessianAtIdentity (fun V : TorusField n => ∑ z ∈ sitesInBlocks R.params.side {Y},
                responseRemainder A.cold (n * R.params.side) z h (ResponseInTheExpansion.coldFieldAboveFrames R V 0)) b b' -
              A.coeff * hessianAtIdentity (fun V : TorusField n => ∑ z ∈ sitesInBlocks R.params.side {Y},
                (blockMean R.params.side R.depth (n * R.params.side) z h - blockMean R.params.side (R.depth + 1) n Y h) *
                  levelShare R.params.coupling R.params.side R.depth Finset.univ z
                    (ResponseInTheExpansion.coldFieldAboveFrames R V 0)) b b'| ≤
            C₂ * R.coupling ^ (-(1 / 2) : ℝ) * weightLipschitz R.params.side (R.depth + 1) h /
              R.params.weight (tripleDiam Y b b')
end YangMills.Construction.WeightedResponses
end
