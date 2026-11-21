import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Functions.WeightedModulusSum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LogBounds
open WeightedModulusSum TorusBoundNotation
variable {n : ℕ}
def sublevelSet (w : Weights n) (Q : ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {z | w.weightedNorm z < (Q + 1)⁻¹}
def logOf (h : Coordinates.ComplexCoordinates n → ℂ) : Coordinates.ComplexCoordinates n → ℂ :=
  fun z => principalLog (h z)
def BoundedLogEstimate : Prop :=
  ∀ (n : ℕ) (w : Weights n) (h : Coordinates.ComplexCoordinates n → ℂ) (Q : ℝ),
    ComplexVariables.IsHolomorphicScalar w.unitSet h → h 0 = 1 → (∀ z ∈ w.unitSet, ‖h z‖ ≤ Q) →
    1 ≤ Q ∧
    (∀ z ∈ w.unitSet,
      ‖h z - 1‖ ≤ min ((Q + 1) * w.weightedNorm z)
        (Q * w.weightedNorm z * (1 - w.weightedNorm z)⁻¹)) ∧
    ((∀ z ∈ sublevelSet w Q, ‖h z - 1‖ < 1 ∧ h z ≠ 0) ∧
      ComplexVariables.IsHolomorphicScalar (sublevelSet w Q) (logOf h) ∧
      (∀ z ∈ sublevelSet w Q, Complex.exp (logOf h z) = h z) ∧
      logOf h 0 = 0 ∧
      Q / (2 * Q + 1) < 1 / 2 ∧
      ∀ z, w.weightedNorm z ≤ 1 / 2 * (Q + 1)⁻¹ →
        ‖h z - 1‖ ≤ Q / (2 * Q + 1) ∧ 1 / 2 < ‖h z‖ ∧ ‖h z‖ < 3 / 2 ∧
          ‖logOf h z‖ ≤ Real.log 2) ∧
    ‖mixedDeriv (logOf h) 0‖ ≤
      Real.log 2 * (2 * Q + 2) ^ n * (n : ℝ) ^ n * ∏ i, w.c i
end YangMills.Construction.LogBounds
