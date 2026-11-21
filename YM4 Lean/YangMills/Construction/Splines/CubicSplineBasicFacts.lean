import YangMills.Construction.Splines.TentAndCubicSplineDensity
import Mathlib
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Splines
def TentConvolutionFacts : Prop :=
  (∀ x : ℝ, tentFunction x = max 0 (1 / 2 - |x|)) ∧
  realConvolution tentFunction tentFunction 0 = 1 / 12 ∧
  ∀ x : ℝ, cubicSpline x =
    realConvolution tentFunction tentFunction x / realConvolution tentFunction tentFunction 0
def CubicSplineShapeFacts : Prop :=
  (∀ x : ℝ, 0 ≤ cubicSpline x) ∧
  (∀ x : ℝ, cubicSpline (-x) = cubicSpline x) ∧
  tsupport cubicSpline ⊆ Icc (-1) 1 ∧
  ContDiff ℝ 1 cubicSpline ∧
  (∀ x : ℝ, cubicSpline x ≤ cubicSpline 0) ∧
  cubicSpline 0 = 1
def CubicSplineFourierFacts : Prop :=
  (∀ ξ : ℝ, ∫ x : ℝ, (cubicSpline x : ℂ) * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) =
    (cubicSplineIntegral : ℂ) * ((Real.sinc (ξ / 4) : ℝ) : ℂ) ^ 4) ∧
  cubicSplineIntegral = 3 / 4 ∧
  0 < cubicSplineIntegral
def SplineDensityFacts : Prop :=
  (∀ x : ℝ, 0 ≤ splineDensity x) ∧
  (∀ x : ℝ, splineDensity (-x) = splineDensity x) ∧
  ContDiff ℝ 1 splineDensity ∧
  tsupport splineDensity ⊆ Icc (-(1 / 8)) (1 / 8) ∧
  ∫ x : ℝ, splineDensity x = 1 ∧
  ∀ x : ℝ, splineDensity x = cubicSpline (8 * x) / ∫ y : ℝ, cubicSpline (8 * y)
def CubicSplineBasicFacts : Prop :=
  TentConvolutionFacts ∧ CubicSplineShapeFacts ∧ CubicSplineFourierFacts ∧ SplineDensityFacts
end YangMills.Construction.Splines
