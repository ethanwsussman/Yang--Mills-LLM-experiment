import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion MarkedIntegrals
namespace MomentLaw
variable {ℓ : StepParameters}
def coldAlongSteps (T : StageTower ℓ) (s : ℕ) (m : ℝ) :
    (D n : ℕ) → [NeZero n] → MarkedSample ℓ (s + D) n → TorusSite (fineSide ℓ.side D n) → Prop
  | 0, _, _, _, _ => True
  | D + 1, n, _, u, o =>
    IsColdOnBall ℓ.threshold u.2.2.1 (siteAbove ℓ.side (D + 1) n o) m ∧
      (∀ b ∈ chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (D + 1) n o) m),
        ‖(stepDeviation T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) b : ℍ[ℝ])‖ < ℓ.threshold / 64) ∧
      coldAlongSteps T s m D (n * ℓ.side) u.1 o
def deviationsBoundedAlong (T : StageTower ℓ) (s : ℕ) (nn ρ₀ τ : ℝ) :
    (D n : ℕ) → [NeZero n] → MarkedSample ℓ (s + D) n → TorusSite (fineSide ℓ.side D n) → Prop
  | 0, _, _, _, _ => True
  | D + 1, n, _, u, o =>
    maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
        ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) ≤ τ ∧
      deviationsBoundedAlong T s nn ρ₀ τ D (n * ℓ.side) u.1 o
def readBondsAtLevel (ℓ : StepParameters) (nn ρ₀ : ℝ) (d n : ℕ) [NeZero n]
    (o : TorusSite (fineSide ℓ.side (d + 1) n)) : Finset (TorusBond (n * ℓ.side)) :=
  chartBondsInBlocks ℓ.side (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀))
def deviationMass (T : StageTower ℓ) (k : ℕ) (nn ρ₀ ρA : ℝ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (k + d) n → TorusSite (fineSide ℓ.side d n) →
      TorusPlaquette (fineSide ℓ.side d n) → ℝ
  | 0, _, _, _, _, _ => 0
  | d + 1, n, _, u, o, p =>
    deviationMass T k nn ρ₀ ρA d (n * ℓ.side) u.1 o p +
      ∑ b ∈ readBondsAtLevel ℓ nn ρ₀ d n o,
        |adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b| *
          ‖(stepDeviation T (k + d) u.2.2.1 (topField ℓ (k + d) (n * ℓ.side) u.1) b : ℍ[ℝ])‖
end MomentLaw
end YangMills.Construction
end
