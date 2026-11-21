import YangMills.Construction.TwoPoints.TestPlatesAtAWidthAndTheNumbersOfTheGrowthBound
import Mathlib
open Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.DilationAveraging
open YangMills.Construction.Splines (cubicSplineIntegral)
open YangMills.Construction.TwoPoints.TestPlates (averageLowerConst scaledSplineFourier scaledFrequency)
def Statement : Prop :=
  0 < averageLowerConst ∧
  ∀ w : ℝ, 0 < w →
    (∀ q : ℝ, averageLowerConst * w ^ 2 * (1 + w ^ 2 * q ^ 2) ^ (-4 : ℤ) ≤
      ∫ κ in (1 : ℝ)..2, (scaledSplineFourier w κ q).re ^ 2) ∧
    (∀ q : ℝ, ∀ κ ∈ Icc (1 : ℝ) 2, scaledSplineFourier w κ q =
      ((1 / 4 * κ * w * cubicSplineIntegral * Real.sinc (scaledFrequency w κ q) ^ 4 : ℝ) : ℂ)) ∧
    (∀ q : ℝ, ∀ κ ∈ Icc (1 : ℝ) 2, (scaledSplineFourier w κ q).im = 0) ∧
    ContinuousOn (fun p : ℝ × ℝ => scaledSplineFourier w p.1 p.2) (Icc (1 : ℝ) 2 ×ˢ univ)
end YangMills.Construction.TwoPoints.DilationAveraging
