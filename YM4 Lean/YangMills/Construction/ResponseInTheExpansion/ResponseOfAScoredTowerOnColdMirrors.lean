import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheChainOnColdMirrors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open Classical
def scoredTowerColdMirrorResponseAt (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∀ Kr : WeightedResponses.ResponseParameters, Kr.Admissible (Tb.stepParameters y) → ∃ C c x₀ : ℝ, 0 < c ∧
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (S : FreeEnergies.ScoredStageTower T) (β : ℝ)
      (k tp N : ℕ) [NeZero N] (nn : ℝ)
      (o : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
        (WeightedResponses.fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)))
      (m : ℕ) [NeZero (4 * m)],
      IsLocalChainAbove Tb y T β k N nn x₀ → (Tb.stepParameters y).side ∣ N → k ≤ tp → S.params = Kr →
      S.FollowsFlow β tp →
      (TorusLumps.clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) / 64 ≤ m →
      12 * nn + m ≤ localBoxRadius (flowCouplings (Tb.stepParameters y) β k) →
      ∀ h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide (Tb.stepParameters y).side k
          (WeightedResponses.fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
          (WeightedResponses.fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))),
        (∀ z p, z ∉ supBall o (12 * nn) → WeightedResponses.IsPlaquetteAt (Tb.stepParameters y).side k z p → h p = 0) →
        ∃ κ₀ : ℝ, ∀ h' : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
            (WeightedResponses.fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) →
            WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide (Tb.stepParameters y).side k (4 * m)),
          (∀ z ∈ weightSupportSites (Tb.stepParameters y).side k _ h,
            WeightedResponses.WeightsAgreeAt (Tb.stepParameters y).side k z (0 : TorusFields.TorusSite (4 * m)) h (h' z)) →
          ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β
              (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N),
            IsLocalEvent T k (localChainDepth (Tb.stepParameters y) β k)
              (localBoxRadius (flowCouplings (Tb.stepParameters y) β k)) N u o →
            (∀ z ∈ weightSupportSites (Tb.stepParameters y).side k _ h,
              TorusFields.IsCold (Tb.stepParameters y).threshold
                (TorusMirror.mirrorField m z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u))) ∧
            |WeightedResponses.response T β S.coeffs k _ h
                (sampleBelow (Tb.stepParameters y) k (localChainDepth (Tb.stepParameters y) β k) _
                  (sampleBelow (Tb.stepParameters y) (k + localChainDepth (Tb.stepParameters y) β k)
                    (localChainDepth (Tb.stepParameters y) β k) N u)) - κ₀ -
              ∑ z ∈ weightSupportSites (Tb.stepParameters y).side k _ h,
                WeightedResponses.centeredResponse
                  (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k)
                  (4 * m) 0 (TorusMirror.mirrorField m z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) (h' z)| ≤
              C * nn ^ 4 * Real.exp (-(c * m)) * WeightedResponses.weightNorm (Tb.stepParameters y).side k h
def scoredTowerColdMirrorResponseStatement : Prop :=
  HoldsOnParameterFamilies scoredTowerColdMirrorResponseAt
end YangMills.Construction.ResponseInTheExpansion
end
