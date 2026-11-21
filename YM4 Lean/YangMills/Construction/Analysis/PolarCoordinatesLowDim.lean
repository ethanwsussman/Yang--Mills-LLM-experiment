import Mathlib
open MeasureTheory Metric Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Analysis.PolarCoordinates
variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
abbrev sphereMeasure : Measure (sphere (0 : E) 1) := (volume : Measure E).toSphere
def LintegralFormula (d : ℕ) : Prop :=
  ∀ f : E → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x = ∫⁻ ω : sphere (0 : E) 1,
      (∫⁻ r in Ioi (0 : ℝ), f (r • (ω : E)) * ENNReal.ofReal (r ^ (d - 1))) ∂sphereMeasure E
def IntegralFormula (d : ℕ) : Prop :=
  ∀ f : E → ℝ, Integrable f →
    (∀ᵐ ω : sphere (0 : E) 1 ∂sphereMeasure E,
      IntegrableOn (fun r : ℝ => f (r • (ω : E)) * r ^ (d - 1)) (Ioi 0)) ∧
    Integrable (fun ω : sphere (0 : E) 1 => ∫ r in Ioi (0 : ℝ), f (r • (ω : E)) * r ^ (d - 1))
      (sphereMeasure E) ∧
    ∫ x, f x = ∫ ω : sphere (0 : E) 1,
      (∫ r in Ioi (0 : ℝ), f (r • (ω : E)) * r ^ (d - 1)) ∂sphereMeasure E
def RadialLintegralFormula (d : ℕ) (A : ℝ) : Prop :=
  ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : E, g ‖x‖ =
      ENNReal.ofReal A * ∫⁻ r in Ioi (0 : ℝ), g r * ENNReal.ofReal (r ^ (d - 1))
def RadialIntegralFormula (d : ℕ) (A : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Integrable (fun x : E => g ‖x‖) →
    IntegrableOn (fun r : ℝ => g r * r ^ (d - 1)) (Ioi 0) ∧
    ∫ x : E, g ‖x‖ = A * ∫ r in Ioi (0 : ℝ), g r * r ^ (d - 1)
def PolarFormulas (d : ℕ) (A : ℝ) : Prop :=
  LintegralFormula E d ∧ IntegralFormula E d ∧
    sphereMeasure E univ = ENNReal.ofReal A ∧
    RadialLintegralFormula E d A ∧ RadialIntegralFormula E d A
def PolarCoordinatesDimThreeFour : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E],
    (Module.finrank ℝ E = 3 → PolarFormulas E 3 (4 * Real.pi)) ∧
    (Module.finrank ℝ E = 4 → PolarFormulas E 4 (2 * Real.pi ^ 2))
end YangMills.Construction.Analysis.PolarCoordinates
