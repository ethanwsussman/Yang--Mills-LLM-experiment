import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
open Coordinates
def DominatedIntegralHolomorphicAndDeriv : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ), 1 ≤ n →
    ∀ (W : Set (ComplexCoordinates n)), IsOpen W →
    ∀ (g : ComplexCoordinates n → Ω → ℂ) (h : Ω → ℝ),
      (∀ z ∈ W, Measurable (g z)) →
      (∀ ω, ComplexCoordinates.IsHolomorphicIn (N' := 1) W fun z _ => g z ω) →
      (∀ z ∈ W, ∀ ω, ‖g z ω‖ ≤ h ω) →
      Integrable h μ →
      ComplexCoordinates.IsHolomorphicIn (N' := 1) W (fun z _ => ∫ ω, g z ω ∂μ) ∧
        ∀ z ∈ W, ∀ j : Fin n,
          Integrable (fun ω =>
            deriv (fun ζ : ℂ => g (z + ζ • ComplexCoordinates.stdBasisVector j) ω) 0) μ ∧
            deriv (fun ζ : ℂ => ∫ ω, g (z + ζ • ComplexCoordinates.stdBasisVector j) ω ∂μ) 0 =
              ∫ ω, deriv (fun ζ : ℂ => g (z + ζ • ComplexCoordinates.stdBasisVector j) ω) 0 ∂μ
end YangMills.Construction.ComplexAnalysis
