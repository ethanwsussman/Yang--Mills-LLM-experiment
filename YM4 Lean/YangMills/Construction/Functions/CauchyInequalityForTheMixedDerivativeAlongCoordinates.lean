import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Functions.WeightedModulusSum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CauchyEstimates
def closedPolydisk {n : ℕ} (r : Fin n → ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {z | ∀ i, ‖z i‖ ≤ r i}
def MixedDerivBoundOnClosedPolydisk : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ r : Fin n → ℝ, (∀ i, 0 < r i) →
    ∀ (U : Set (Coordinates.ComplexCoordinates n)) (F : Coordinates.ComplexCoordinates n → ℂ) (B : ℝ),
      ComplexVariables.IsHolomorphicScalar U F → closedPolydisk r ⊆ U → 0 ≤ B →
        (∀ z ∈ closedPolydisk r, ‖F z‖ ≤ B) →
          ‖TorusBoundNotation.mixedDeriv F 0‖ ≤ B * ∏ i, (r i)⁻¹
def MixedDerivBoundOnWeightedSet : Prop :=
  ∀ (n : ℕ) (w : WeightedModulusSum.Weights n) (F : Coordinates.ComplexCoordinates n → ℂ) (B : ℝ),
    ComplexVariables.IsHolomorphicScalar w.unitSet F → 0 ≤ B → (∀ z ∈ w.unitSet, ‖F z‖ ≤ B) →
      ‖TorusBoundNotation.mixedDeriv F 0‖ ≤ B * (n : ℝ) ^ n * ∏ i, w.c i
def MixedDerivCauchyBound : Prop := MixedDerivBoundOnClosedPolydisk ∧ MixedDerivBoundOnWeightedSet
end YangMills.Construction.CauchyEstimates
