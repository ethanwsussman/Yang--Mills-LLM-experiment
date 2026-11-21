import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Torus.FourierBox
open AmbientPoints Conventions
def modesWithSupNorm (D m : ℕ) : Set (Fin D → ℤ) := {k | supNormInt k = m}
section Statements
variable (s : StandingParameters) (p : ℕ) (L : ℝ)
def FourierCoeffIsLinear : Prop :=
  ∀ μ : Fin (4 * p) → ℤ,
    IsComplexLinearForm fun g : testFns (fundamentalBoxPow s p L) => fourierCoeff L g.1 μ
def FourierCoeffEstimatesOf (g : Tuple s .euclidean p → ℂ) : Prop :=
  (∀ μ, ENNReal.ofReal ‖fourierCoeff L g μ‖ ≤ tupleSupNorm g) ∧
  (∀ (i : Fin (4 * p)) μ,
    fourierCoeff L (multiDeriv (Pi.single i 1) g) μ =
      2 * Real.pi * Complex.I * (μ i : ℂ) / (L : ℂ) * fourierCoeff L g μ) ∧
  (∀ μ, μ ≠ 0 → ∀ q : ℕ,
    ENNReal.ofReal ‖fourierCoeff L g μ‖ ≤
      ENNReal.ofReal ((L / (2 * Real.pi * (supNormInt μ : ℝ))) ^ q) * cnNorm q g) ∧
  ∀ t : ℝ, 0 ≤ t →
    Summable fun μ : Fin (4 * p) → ℤ => ‖fourierCoeff L g μ‖ * (1 + (supNormInt μ : ℝ)) ^ t
def ShellOfModesCount : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    let outer : ℤ := (2 * (r : ℤ) + 1) ^ (4 * p)
    let inner : ℤ := (2 * (r : ℤ) - 1) ^ (4 * p)
    (modesWithSupNorm (4 * p) r).Finite ∧
    ((modesWithSupNorm (4 * p) r).ncard : ℤ) = outer - inner ∧
    outer - inner ≤ 2 * (4 * (p : ℤ)) * (2 * (r : ℤ) + 1) ^ (4 * p - 1) ∧
    2 * (4 * (p : ℤ)) * (2 * (r : ℤ) + 1) ^ (4 * p - 1) ≤
      2 * (4 * (p : ℤ)) * (3 * (r : ℤ)) ^ (4 * p - 1)
def FourierCoeffOfTensorProduct : Prop :=
  ∀ φ : Fin p → Pt s .euclidean → ℂ,
    (∀ i, ofSinglePoint (φ i) ∈ testFns (fundamentalBoxPow s 1 L)) →
      tensorProd φ ∈ testFns (fundamentalBoxPow s p L) ∧
      ∀ μ : Fin (4 * p) → ℤ,
        fourierCoeff L (tensorProd φ) μ =
          ∏ i, fourierCoeff (n := 1) L (ofSinglePoint (φ i)) (blockOf μ i)
end Statements
def FourierCoeffBounds : Prop :=
  ∀ (s : StandingParameters) (p : ℕ) (L : ℝ), 1 ≤ p → 0 < L →
    FourierCoeffIsLinear s p L ∧
    (∀ g ∈ testFns (fundamentalBoxPow s p L), FourierCoeffEstimatesOf s p L g) ∧
    ShellOfModesCount p ∧
    FourierCoeffOfTensorProduct s p L
end YangMills.Construction.Torus.FourierBox
