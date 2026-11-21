import YangMills.Construction.SpectralMeasures.EuclideanComplexMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.EuclideanBorel
def gaussianDecay {n : ℕ} (ε : ℝ) (v : Space n) : ℝ :=
  Real.exp (-(ε * ‖v‖ ^ 2) / 2)
def heatKernel {n : ℕ} (ε : ℝ) (y : Space n) : ℝ :=
  (2 * Real.pi * ε) ^ (-(n : ℝ) / 2) * Real.exp (-(‖y‖ ^ 2) / (2 * ε))
def boundedlySupportedContinuous (n : ℕ) : Set (Space n → ℂ) :=
  {h | Continuous h ∧ ∃ B : Set (Space n), Bornology.IsBounded B ∧ ∀ y, y ∉ B → h y = 0}
def heatKernelConv {n : ℕ} (h : Space n → ℂ) (ε : ℝ) (y : Space n) : ℂ :=
  ∫ y', h y' * (heatKernel ε (y - y') : ℂ)
def fourierOfFn {n : ℕ} (h : Space n → ℂ) (v : Space n) : ℂ :=
  ∫ y', h y' * Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ)))
def fourierOfMeasure {n : ℕ} (ν : BorelSubset n → ℂ) (v : Space n) : ℂ :=
  complexIntegral ν fun y => Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ))
def planeUnitCircle : Set (Space 2) :=
  {y | ‖y‖ = 1}
def circleChar (k : ℤ) : Space 2 → ℂ :=
  planeUnitCircle.indicator fun y => ((y 0 : ℂ) + Complex.I * (y 1 : ℂ)) ^ k
end YangMills.Construction.EuclideanBorel
