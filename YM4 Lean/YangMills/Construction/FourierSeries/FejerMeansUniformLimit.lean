import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FourierSeries
def fourierCoeffOnCircle (f : ℝ → ℂ) (k : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ u in (-Real.pi)..Real.pi, f u * Complex.exp (-((k : ℂ) * (u : ℂ) * Complex.I))
def symmetricPartialSum (f : ℝ → ℂ) (t : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
    fourierCoeffOnCircle f k * Complex.exp ((k : ℂ) * (x : ℂ) * Complex.I)
def cesaroMeanOfPartialSums (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ * ∑ t ∈ Finset.range (n + 1), symmetricPartialSum f t x
def IsTwoPiPeriodicInEachCoord {d : ℕ} (f : (Fin d → ℝ) → ℂ) : Prop :=
  ∀ (j : Fin d) (x : Fin d → ℝ), f (Function.update x j (x j + 2 * Real.pi)) = f x
def fourierCoeffOnTorus {d : ℕ} (f : (Fin d → ℝ) → ℂ) (k : Fin d → ℤ) : ℂ :=
  ((2 * (Real.pi : ℂ)) ^ d)⁻¹ *
    ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi),
      f x * Complex.exp (-((∑ j, (k j : ℂ) * (x j : ℂ)) * Complex.I))
def FejerTheoremAndTorusUniqueness : Prop :=
  (∀ f : ℝ → ℂ, Continuous f → Function.Periodic f (2 * Real.pi) →
    TendstoUniformly (cesaroMeanOfPartialSums f) f Filter.atTop) ∧
  (∀ (d : ℕ) (f g : (Fin d → ℝ) → ℂ), Continuous f → Continuous g →
    IsTwoPiPeriodicInEachCoord f → IsTwoPiPeriodicInEachCoord g →
    (∀ k : Fin d → ℤ, fourierCoeffOnTorus f k = fourierCoeffOnTorus g k) → f = g)
end YangMills.Construction.FourierSeries
