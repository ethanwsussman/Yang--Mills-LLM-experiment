import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
open TorusLumps TorusFields RenormalizationStepParameters WeightedResponses
open Classical
def quadraticResponseAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ Kr : ResponseParameters, Kr.Admissible (Tb.stepParameters y) → ∃ (Cq xq : ℕ → ℝ) (C δ c x₀ : ℝ), 0 < δ ∧ 0 < c ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (S : FreeEnergies.ScoredStageTower T) (β : ℝ) (k tp N : ℕ) [NeZero N]
      (r v : ℝ) (α : ℕ → ℝ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
      IsLocalChainAbove Tb y T β k N r x₀ → (Tb.stepParameters y).side ∣ N →
      IsChainResponseCoeff (Tb.stepParameters y) Kr β k α → |α k| ≤ 2 → k ≤ tp → S.params = Kr →
      S.FollowsFlow β tp → S.coeffs = α → 0 < v → v ≤ 1 → 2 ≤ v * r →
      ∃ ka : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) →
          TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) →
          TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) → ℝ,
        IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) δ C ka ∧
        IsNormalizedShareForm (Real.exp (-(c * logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) ka ∧
        ∀ h : PlaquetteWeight (fineSide (Tb.stepParameters y).side k
            (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
              (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
          weightSup h ≤ 1 → weightLipschitz (Tb.stepParameters y).side k h ≤ 2 / (v * r) →
          (∀ (z : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
              (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))) (p),
            z ∉ supBall o (12 * r) → IsPlaquetteAt (Tb.stepParameters y).side k z p → h p = 0) →
          ∃ (κ₀ : ℝ) (kr : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
                (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) →
              TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
                (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) →
              TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
                (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) → ℝ),
            IsLocalKernel (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) δ
              (C * ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) + 1 / (v * r))) kr ∧
            (∀ z, z ∉ weightSupportSites (Tb.stepParameters y).side k _ h → ∀ p p', kr z p p' = 0) ∧
            ∀ q : ℕ, 1 ≤ q → xq q ≤ (couplingFlow (Tb.stepParameters y) β k).1 →
              ∫⁻ u, ENNReal.ofReal (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
                    (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o ∧
                  IsGaugeSmallAlong T k r (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)
                    ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 4 : ℝ)))
                    (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
                    (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
                    (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1))
                      (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) o
                    (axialGaugeAt (Tb.stepParameters y)
                      (topField (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1))
                        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
                        (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1))
                          (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u))
                      (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
                        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o))}
                (fun u => |response T β α k _ h (sampleBelow (Tb.stepParameters y) k
                    (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) _ (sampleBelow (Tb.stepParameters y)
                      (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1))
                      (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u)) - κ₀ -
                  (1 / 2) * ∑ z, ∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ,
                    (blockMean (Tb.stepParameters y).side k _ z h * α k * ka z p p' + kr z p p') * ∑ e : Fin 3,
                      imaginaryComponent e (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) r
                        (couplingFlow (Tb.stepParameters y) β k).1 N u o p) *
                      imaginaryComponent e (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) r
                        (couplingFlow (Tb.stepParameters y) β k).1 N u o p')| ^ (2 * q)) u)
                ∂(markedSampleLaw T β (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) +
                  (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) N) ≤
              ENNReal.ofReal ((Cq q * r ^ 4 * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * q))
def quadraticResponseStatement : Prop :=
  HoldsOnParameterFamilies quadraticResponseAt
end ResponseInTheExpansion
end YangMills.Construction
end
