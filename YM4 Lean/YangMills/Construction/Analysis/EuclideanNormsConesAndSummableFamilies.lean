import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Euclidean
def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, x j ^ 2)
def euclidSetDist {n : ℕ} (A A' : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ x ∈ A, ⨅ x' ∈ A', ENNReal.ofReal (euclidNorm (x - x'))
def compactSupportContinuous (X 𝕜 : Type*) [TopologicalSpace X] [TopologicalSpace 𝕜] [Zero 𝕜] :
    Set (X → 𝕜) :=
  {f | Continuous f ∧ HasCompactSupport f}
def IsAffineIsometryR4 (f : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ Q ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ b : Fin 4 → ℝ, ∀ x, f x = (Q : Matrix _ _ ℝ).mulVec x + b
end YangMills.Construction.Euclidean
