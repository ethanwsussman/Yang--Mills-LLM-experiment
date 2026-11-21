import YangMills.Construction.SpectralMeasures.GaussianAndCircleCharacters
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanBorel
def planeUnitCircleBorel : BorelSubset 2 :=
  ⟨planeUnitCircle, (isClosed_eq continuous_norm continuous_const).measurableSet⟩
def GaussianFourierIdentities (n : ℕ) (ε : ℝ) : Prop :=
  (∀ y : Space n,
    ∫ v : Space n, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) * (gaussianDecay ε v : ℂ) =
      (((2 * Real.pi) ^ n * heatKernel ε y : ℝ) : ℂ)) ∧
  (∀ v : Space n,
    ∫ y : Space n, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
      (heatKernel ε y : ℂ) = (gaussianDecay ε v : ℂ)) ∧
  ∫ y : Space n, heatKernel ε y = 1
def HeatKernelConvProperties {n : ℕ} (h : Space n → ℂ) (ε : ℝ) : Prop :=
  Continuous (heatKernelConv h ε) ∧
  Tendsto (heatKernelConv h ε) (comap (fun y => ‖y‖) atTop) (𝓝 0) ∧
  (∀ y, ‖heatKernelConv h ε y‖ ≤ ⨆ y', ‖h y'‖) ∧
  Integrable (heatKernelConv h ε) ∧
  ∫ y, ‖heatKernelConv h ε y‖ ≤ ∫ y, ‖h y‖ ∧
  ((∀ y, (h y).im = 0 ∧ 0 ≤ (h y).re) →
    ∀ y, (heatKernelConv h ε y).im = 0 ∧ 0 ≤ (heatKernelConv h ε y).re)
def FourierOfFnProperties {n : ℕ} (h : Space n → ℂ) : Prop :=
  Continuous (fourierOfFn h) ∧
  ∀ v, ‖fourierOfFn h v‖ ≤ ∫ y, ‖h y‖
def MollifiedFourierIdentities {n : ℕ} (h : Space n → ℂ) (ε : ℝ) : Prop :=
  (∀ y : Space n, heatKernelConv h ε y =
    (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ) *
      ∫ v : Space n, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        (gaussianDecay ε v : ℂ) * fourierOfFn h v) ∧
  ∀ v : Space n,
    ∫ y : Space n, heatKernelConv h ε y *
      Complex.exp (-(Complex.I * ((inner ℝ v y : ℝ) : ℂ))) =
    (gaussianDecay ε v : ℂ) * fourierOfFn h v
def FourierOfMeasureProperties {n : ℕ} (ν : BorelSubset n → ℂ) : Prop :=
  Continuous (fourierOfMeasure ν) ∧
  ∃ C : ℝ, ∀ v, ‖fourierOfMeasure ν v‖ ≤ C
def IntegralOfMollified {n : ℕ} (ν : BorelSubset n → ℂ) (h : Space n → ℂ) (ε : ℝ) : Prop :=
  complexIntegral ν (heatKernelConv h ε) =
    (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ) *
      ∫ v : Space n, (gaussianDecay ε v : ℂ) * fourierOfFn h v * fourierOfMeasure ν v
def DeterminingFamiliesStatement : Prop :=
  (∀ (n : ℕ), 1 ≤ n →
    (∀ ε : ℝ, 0 < ε → GaussianFourierIdentities n ε) ∧
    (∀ h ∈ boundedlySupportedContinuous n,
      (∀ ε : ℝ, 0 < ε → HeatKernelConvProperties h ε ∧ MollifiedFourierIdentities h ε) ∧
      Tendsto (fun ε : ℝ => ⨆ y, ‖heatKernelConv h ε y - h y‖) (𝓝[>] 0) (𝓝 0) ∧
      FourierOfFnProperties h) ∧
    ∀ ν : BorelSubset n → ℂ, IsFiniteCombinationMeasure ν →
      FourierOfMeasureProperties ν ∧
      (∀ h ∈ boundedlySupportedContinuous n, ∀ ε : ℝ, 0 < ε →
        IntegralOfMollified ν h ε) ∧
      ((∀ h' ∈ boundedlySupportedContinuous n, complexIntegral ν h' = 0) → IsZeroMeasure ν) ∧
      ((∀ v, fourierOfMeasure ν v = 0) → IsZeroMeasure ν)) ∧
  ∀ ν : BorelSubset 2 → ℂ, IsFiniteCombinationMeasure ν → IsSupportedOn ν planeUnitCircleBorel →
    (∀ k : ℤ, complexIntegral ν (circleChar k) = 0) → IsZeroMeasure ν
end YangMills.Construction.EuclideanBorel
