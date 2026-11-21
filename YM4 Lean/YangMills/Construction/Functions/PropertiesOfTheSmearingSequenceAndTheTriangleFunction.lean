import YangMills.Construction.Functions.TriangleKernel
import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TriangleKernel
open Real
open YangMills.Construction.ReflectionPositivity.EnergyMomentum (distTwoPiInt)
def SeqAndTentProperties : Prop :=
  ((∀ j : ℤ, smearingSeq (-j) = smearingSeq j) ∧
    smearingSeq 0 = 0 ∧
    ∀ j : ℤ, (smearingSeq j : ℂ) =
      1 / 2 * Complex.I ^ j - (-1 : ℂ) ^ j + 1 / 2 * (-Complex.I) ^ j) ∧
  (Continuous tentFunction ∧
    (∀ u : ℝ, 0 ≤ tentFunction u ∧ tentFunction u ≤ tentFunction 0) ∧
    tentFunction 0 = 8 ∧
    (∀ u : ℝ, π / 4 ≤ distTwoPiInt u → tentFunction u = 0) ∧
    (1 / (2 * π) * ∫ u in (-π)..π, tentFunction u) = 1) ∧
  (tentFourierCoeff 0 = 1 ∧
    (∀ j : ℤ, j ≠ 0 → tentFourierCoeff j =
      (((Real.sin ((j : ℝ) * π / 8) / ((j : ℝ) * π / 8)) ^ 2 : ℝ) : ℂ)) ∧
    (∀ j : ℤ, tentFourierCoeff j = tentFourierCoeff (-j)) ∧
    (∀ j : ℤ, (tentFourierCoeff j).im = 0 ∧ 0 ≤ (tentFourierCoeff j).re) ∧
    (∀ j : ℤ, j ≠ 0 → (tentFourierCoeff j).re ≤ 64 / (π * (j : ℝ)) ^ 2) ∧
    Summable fun j : ℤ => (tentFourierCoeff j).re) ∧
  ((∀ u : ℝ, HasSum
      (fun j : ℤ => tentFourierCoeff j * Complex.exp (Complex.I * j * u))
      (tentFunction u : ℂ)) ∧
    (∀ u : ℝ, Summable
      fun j : ℤ => ‖tentFourierCoeff j * Complex.exp (Complex.I * j * u)‖) ∧
    TendstoUniformly
      (fun (s : Finset ℤ) (u : ℝ) =>
        ∑ j ∈ s, tentFourierCoeff j * Complex.exp (Complex.I * j * u))
      (fun u : ℝ => (tentFunction u : ℂ)) Filter.atTop) ∧
  ((Summable fun j : ℤ => |(smearingSeq j : ℝ)| * (tentFourierCoeff j).re) ∧
    (∀ j : ℤ, ((smearingSeq j : ℂ) * tentFourierCoeff j).im = 0) ∧
    (∀ j : ℤ, (smearingSeq (-j) : ℂ) * tentFourierCoeff (-j) =
      (smearingSeq j : ℂ) * tentFourierCoeff j) ∧
    (smearingSeq 0 : ℂ) * tentFourierCoeff 0 = 0)
end YangMills.Construction.TriangleKernel
