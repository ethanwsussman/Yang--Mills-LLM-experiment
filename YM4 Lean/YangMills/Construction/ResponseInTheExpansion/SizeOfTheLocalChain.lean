import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters TorusFields TorusLumps WeightedResponses
open Classical
open MeasureTheory
variable {ℓ : TorusLumps.StepParameters}
def widenedStageSum (T : StageTower ℓ) (t : ℕ) (nn ρ₀ : ℝ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (t + d) n → TorusSite (fineSide ℓ.side d n) → ℝ
  | 0, _, _, _, _ => 0
  | d + 1, n, _, u, o =>
    maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) + 1) +
      maxDeviationOnBall T (t + d) u.2.2.1 (topField ℓ (t + d) (n * ℓ.side) u.1) (siteAbove ℓ.side (d + 1) n o)
        ((ballRadius ℓ.side nn ρ₀ d + 1) / (ℓ.side : ℝ) + 2) +
      widenedStageSum T t nn ρ₀ d (n * ℓ.side) u.1 o
def widenedStageMax (t : ℕ) (nn ρ₀ : ℝ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (t + d) n → TorusSite (fineSide ℓ.side d n) → ℝ
  | 0, _, _, u, o => maxCurvatureOnBall (topField ℓ t _ u) o (ballRadius ℓ.side nn ρ₀ 0 + 1)
  | d + 1, n, _, u, o =>
    max (maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) + 1))
      (widenedStageMax t nn ρ₀ d (n * ℓ.side) u.1 o)
def widenedChainSize (T : StageTower ℓ) (C₁ c : ℝ) (M t : ℕ) (nn ρ₀ : ℝ) (d n : ℕ) [NeZero n]
    (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)) : ℝ :=
  min 1 (C₁ * (ρ₀ * maxCurvatureOnBall (topField ℓ (t + d) n u) (siteAbove ℓ.side d n o)
      (ballRadius ℓ.side nn ρ₀ d + 1) +
    widenedStageSum T t nn ρ₀ d n u o + widenedStageMax t nn ρ₀ d n u o + (M : ℝ) * Real.exp (-(c * ρ₀))))
variable (Tb : ParameterAssignment) (y : ℝ)
def localChainSizeAt : Prop :=
  ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧ ∀ q : ℕ, ∃ Cq x₀ : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (t d d' : ℕ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side d (fineSide (Tb.stepParameters y).side d' N))),
      IsLocalChainAbove Tb y T β k N nn x₀ → (Tb.stepParameters y).side ∣ N → k ≤ t →
      t + d = k + localChainDepth (Tb.stepParameters y) β k → d' = localChainDepth (Tb.stepParameters y) β k →
      (∀ s : ℝ, s < 1 → ∀ᵐ u ∂(markedSampleLaw T β (t + d + d') N),
        IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o →
        widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
            (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k) d
            (fineSide (Tb.stepParameters y).side d' N)
            (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o ≤ s →
        IsGaugeSmallAlong T t (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k))
          (localLogScale (Tb.stepParameters y) β k) s d (fineSide (Tb.stepParameters y).side d' N)
          (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o
          (axialGaugeAt (Tb.stepParameters y)
            (topField (Tb.stepParameters y) (t + d) (fineSide (Tb.stepParameters y).side d' N)
              (sampleBelow (Tb.stepParameters y) (t + d) d' N u))
            (siteAbove (Tb.stepParameters y).side d (fineSide (Tb.stepParameters y).side d' N) o))) ∧
      (Integrable (Set.indicator {u | IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o}
          (fun u => widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
            (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k) d
            (fineSide (Tb.stepParameters y).side d' N) (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o ^ q))
          (markedSampleLaw T β (t + d + d') N) ∧
        ∫ u, Set.indicator {u | IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o}
          (fun u => widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
            (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k) d
            (fineSide (Tb.stepParameters y).side d' N) (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o ^ q) u
            ∂(markedSampleLaw T β (t + d + d') N) ≤
        (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ q) ∧
      Integrable (Set.indicator {u | IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o}
          (fun u => maxCurvatureOnBall (topField (Tb.stepParameters y) t _
              (sampleBelow (Tb.stepParameters y) t d _ (sampleBelow (Tb.stepParameters y) (t + d) d' N u))) o
            (ballRadius (Tb.stepParameters y).side (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k))
              (localLogScale (Tb.stepParameters y) β k) 0) ^ q)) (markedSampleLaw T β (t + d + d') N) ∧
      ∫ u, Set.indicator {u | IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o}
          (fun u => maxCurvatureOnBall (topField (Tb.stepParameters y) t _
              (sampleBelow (Tb.stepParameters y) t d _ (sampleBelow (Tb.stepParameters y) (t + d) d' N u))) o
            (ballRadius (Tb.stepParameters y).side (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k))
              (localLogScale (Tb.stepParameters y) β k) 0) ^ q) u ∂(markedSampleLaw T β (t + d + d') N) ≤
        (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 1 / 1000)) ^ q
def localChainSizeStatement : Prop := HoldsOnParameterFamilies localChainSizeAt
end YangMills.Construction.ResponseInTheExpansion
end
