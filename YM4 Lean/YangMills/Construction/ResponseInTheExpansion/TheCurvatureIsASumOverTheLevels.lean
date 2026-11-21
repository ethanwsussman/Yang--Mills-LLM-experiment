import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.WeightedResponses
open Classical
open MeasureTheory
def levelFluctuationSum {ℓ : StepParameters} (T : StageTower ℓ) (k : ℕ) (nn ρ₀ ρA : ℝ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (k + d) n → TorusSite (fineSide ℓ.side d n) →
      (TorusSite n → UnitQuaternion) → TorusPlaquette (fineSide ℓ.side d n) → imaginaryQuaternions
  | 0, _, _, _, _, _, _ => 0
  | d + 1, n, _, u, o, g, p =>
    levelFluctuationSum T k nn ρ₀ ρA d (n * ℓ.side) u.1 o
        (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) p +
      ∑ b : TorusBond (n * ℓ.side), adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b •
        deviationInGauge T (k + d) g
          (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
          (topField ℓ (k + d) (n * ℓ.side) u.1) b
def curvatureLevelSumStatement : Prop :=
  ∀ (ℓ : StepParameters) (T : StageTower ℓ) (ρA : ℝ), (∀ j, (T.stage j).anchorRadius = ρA) →
    ∀ (k : ℕ) (nn ρ₀ : ℝ) (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n))
      (B : TorusBond n → imaginaryQuaternions) (g : TorusSite n → UnitQuaternion) (p : TorusPlaquette (fineSide ℓ.side d n)),
      lieFormCurl (descendedForm T k nn ρ₀ d n u o B g) p =
        levelFluctuationSum T k nn ρ₀ ρA d n u o g p +
          ∑ c : TorusBond n, adjointTransport ℓ.coupling ρA ℓ.side k d n (curlFunctional p) c • B c
end YangMills.Construction.ResponseInTheExpansion
end
