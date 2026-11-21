import YangMills.Construction.EuclideanAnalysis.PowerStripAndGaussianCharacters
import Mathlib
open MeasureTheory
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.Strip
def ModulatedDenseAndMeasureUnique : Prop :=
  (∀ u ∈ stripZeroAtInfty, ∀ ε : ℝ, 0 < ε →
    ∃ v ∈ gaussianModulatedSpan, stripUniformNorm (u - v) ≤ ε) ∧
  (∀ μ ν : Measure UnitStrip, IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∀ (n : ℕ) (t : ℝ),
      ∫ p, (unitStripPow p.1 n : ℂ) * Complex.exp (Complex.I * t * p.2) ∂μ =
        ∫ p, (unitStripPow p.1 n : ℂ) * Complex.exp (Complex.I * t * p.2) ∂ν) →
    μ = ν) ∧
  (∀ μ ν : Measure (Set.Ici (0 : ℝ) × ℝ), IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∀ (n : ℕ) (t : ℝ),
      ∫ p, Complex.exp (-(n : ℂ) * (p.1 : ℝ) + Complex.I * t * p.2) ∂μ =
        ∫ p, Complex.exp (-(n : ℂ) * (p.1 : ℝ) + Complex.I * t * p.2) ∂ν) →
    μ = ν)
end YangMills.Construction.EuclideanAnalysis.Strip
