import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PlaneFields
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
def planeForm (μ ν : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = μ ∧ j = ν then 1 else if i = ν ∧ j = μ then -1 else 0
def LeastActionAtPlaneField : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (t n l : ℕ) [NeZero n] (X : imaginaryQuaternions) (μ ν : Fin 4), 64 ≤ n → ‖X‖ = 1 → μ < ν →
      2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      ∃ V : TorusField n, IsAbelianWithCurvature X (planeForm μ ν) (2 * Real.pi * l / (n : ℝ) ^ 2) V ∧
        actionAtLevel T.coupling T.side (t + 1) Finset.univ V =
          ((n : ℝ) * (T.side : ℝ) ^ (t + 1)) ^ 4 *
            (1 - Real.cos (2 * Real.pi * l / ((n : ℝ) * (T.side : ℝ) ^ (t + 1)) ^ 2))
end YangMills.Construction.PlaneFields
end
