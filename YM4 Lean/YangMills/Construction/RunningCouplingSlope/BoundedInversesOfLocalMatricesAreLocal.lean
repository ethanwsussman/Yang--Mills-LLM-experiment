import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def LocalMatricesBoundedAndInverseLocal : Prop :=
  (∀ θ : ℝ, 0 < θ → ∃ S : ℝ, 0 < S ∧
    ∀ (L n k : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] [DecidableEq ι]
      (c : ι → Tower.Vertex L n k k) (c' : ι' → Tower.Vertex L n k k) (T : Matrix ι' ι ℂ) (M : ℝ),
      Conventions.IsAdmissibleBlockingFactor L → 0 < n → 0 ≤ M →
      IsLocalOnCells c c' T M θ (fun _ => 1) →
      ‖T‖ ≤ S * M) ∧
  ∀ M θ K : ℝ, 0 < M → 0 < θ → 0 < K → ∃ M' θ' : ℝ, 0 < M' ∧ 0 < θ' ∧
    ∀ (L n k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
      (T : Matrix ι ι ℂ), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
      IsLocalOnCells c c T M θ (fun _ => 1) → IsUnit (Matrix.det T) → ‖T⁻¹‖ ≤ K →
      IsLocalOnCells c c T⁻¹ M' θ' (fun _ => 1)
end YangMills.Construction.RunningCouplingSlope
end
