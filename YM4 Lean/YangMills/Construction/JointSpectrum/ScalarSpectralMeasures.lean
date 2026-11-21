import YangMills.Construction.JointSpectrum.FamilyPolynomialCalculus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.JointSpectrum YangMills.Construction.FamilyPolynomials
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace ScalarSpectralMeasures
def sqNormLIntegral {ι : Type*} (μ : Measure (SpectralDomain ι))
    (g : SpectralDomain ι → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ
section SpectralMeasures
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [Nonempty ι]
def IsSpectralMeasureOf (T : CommutingFamily H ι) (v : H) (μ : Measure (SpectralDomain ι)) : Prop :=
  IsFiniteMeasure μ ∧
    ∀ (k : ℕ) (m : ι → ℤ), inner ℂ v (familyMonomial T k m v) = ∫ x, spectralMonomial k m x ∂μ
def spectralMeasure (T : CommutingFamily H ι) (v : H) : Measure (SpectralDomain ι) :=
  Classical.epsilon (IsSpectralMeasureOf T v)
def PolynomialL2Approximation (T : CommutingFamily H ι) (v : H) (g : SpectralDomain ι → ℂ)
    (p : ℕ → SpectralDomain ι → ℂ) : Prop :=
  (∀ i, p i ∈ spectralPolynomials ι) ∧
    Tendsto (fun i => sqNormLIntegral (spectralMeasure T v) (g - p i)) atTop (𝓝 0)
def IsL2CalculusLimit (T : CommutingFamily H ι) (v : H) (g : SpectralDomain ι → ℂ) (w : H) : Prop :=
  ∀ p : ℕ → SpectralDomain ι → ℂ, PolynomialL2Approximation T v g p →
    Tendsto (fun i => polynomialCalculus T (p i) v) atTop (𝓝 w)
def l2Calculus (T : CommutingFamily H ι) (v : H) (g : SpectralDomain ι → ℂ) : H :=
  Classical.epsilon (IsL2CalculusLimit T v g)
end SpectralMeasures
def ScalarSpectralMeasuresStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : Type) [Fintype ι] [Nonempty ι] (T : CommutingFamily H ι),
    Dense {h : C(SpectralDomain ι, ℂ) | (h : SpectralDomain ι → ℂ) ∈ spectralPolynomials ι} ∧
    (∀ (μ : Measure (SpectralDomain ι)) [IsFiniteMeasure μ] (g : SpectralDomain ι → ℂ),
      Measurable g → sqNormLIntegral μ g < ∞ →
        ∃ p : ℕ → SpectralDomain ι → ℂ, (∀ i, p i ∈ spectralPolynomials ι) ∧
          Tendsto (fun i => sqNormLIntegral μ (g - p i)) atTop (𝓝 0)) ∧
    (∀ (μ ν : Measure (SpectralDomain ι)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ (k : ℕ) (m : ι → ℤ), ∫ x, spectralMonomial k m x ∂μ = ∫ x, spectralMonomial k m x ∂ν) →
        μ = ν) ∧
    (∀ v : H,
      IsSpectralMeasureOf T v (spectralMeasure T v) ∧
      (∀ μ, IsSpectralMeasureOf T v μ → μ = spectralMeasure T v) ∧
      spectralMeasure T v univ = ‖v‖ₑ ^ 2 ∧
      ∀ p ∈ spectralPolynomials ι,
        inner ℂ v (polynomialCalculus T p v) = ∫ x, p x ∂(spectralMeasure T v) ∧
        ‖polynomialCalculus T p v‖ₑ ^ 2 = sqNormLIntegral (spectralMeasure T v) p) ∧
    (∀ (c : ℂ) (v : H), spectralMeasure T (c • v) = (‖c‖ₑ ^ 2) • spectralMeasure T v) ∧
    (∀ v w : H,
      spectralMeasure T (v + w) + spectralMeasure T (v - w) =
        (2 : ℝ≥0∞) • spectralMeasure T v + (2 : ℝ≥0∞) • spectralMeasure T w) ∧
    (∀ (v w : H) (E : Set (SpectralDomain ι)), MeasurableSet E →
      spectralMeasure T (v + w) E ≤ 2 * spectralMeasure T v E + 2 * spectralMeasure T w E) ∧
    (∀ (v : H) (g : SpectralDomain ι → ℂ), Measurable g →
      sqNormLIntegral (spectralMeasure T v) g < ∞ →
        IsL2CalculusLimit T v g (l2Calculus T v g) ∧
        (∀ w, IsL2CalculusLimit T v g w → w = l2Calculus T v g) ∧
        (∃ p, PolynomialL2Approximation T v g p) ∧
        ‖l2Calculus T v g‖ₑ ^ 2 = sqNormLIntegral (spectralMeasure T v) g)
end ScalarSpectralMeasures
end YangMills.Construction
