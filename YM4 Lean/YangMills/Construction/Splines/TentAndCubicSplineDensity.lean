import Mathlib
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Splines
def realConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * g (x - y)
def quarterInterval : Set ℝ := Icc (-(1 / 4)) (1 / 4)
def quarterIntervalIndicator : ℝ → ℝ := quarterInterval.indicator 1
def tentFunction : ℝ → ℝ := realConvolution quarterIntervalIndicator quarterIntervalIndicator
def cubicSpline (x : ℝ) : ℝ := 12 * realConvolution tentFunction tentFunction x
def cubicSplineIntegral : ℝ := ∫ x, cubicSpline x
def splineDensity (x : ℝ) : ℝ := 32 / 3 * cubicSpline (8 * x)
end Splines
end YangMills.Construction
