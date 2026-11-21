import YangMills.Construction.Lattice.AxialGauges
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def signedPermMatrices : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {w | ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ), (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
    ∀ (x : Fin 4 → ℝ) (μ : Fin 4), (w *ᵥ x) μ = ε μ * x (σ μ)}
def SignedFrame.toMatrix (r : SignedFrame) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => if ν = r.1 μ then ((r.2 μ : ℤ) : ℝ) else 0
theorem SignedFrame.toMatrix_mulVec (r : SignedFrame) (x : Fin 4 → ℝ) :
    r.toMatrix *ᵥ x = r.actOnVector x := by
  funext μ
  simp [SignedFrame.toMatrix, SignedFrame.actOnVector, Matrix.mulVec, dotProduct]
theorem mem_signedPermMatrices_iff (w : Matrix (Fin 4) (Fin 4) ℝ) :
    w ∈ signedPermMatrices ↔ ∃ r : SignedFrame, w = r.toMatrix := by
  constructor
  · rintro ⟨σ, ε, hε, hw⟩
    refine ⟨(σ, fun μ => if ε μ = 1 then 1 else -1), Matrix.mulVec_injective ?_⟩
    funext x
    rw [SignedFrame.toMatrix_mulVec]
    funext μ
    rw [hw x μ]
    rcases hε μ with hμ | hμ
    · simp [SignedFrame.actOnVector, hμ]
    · have hne : (-1 : ℝ) ≠ 1 := by norm_num
      simp [SignedFrame.actOnVector, hμ, hne]
  · rintro ⟨r, rfl⟩
    refine ⟨r.1, fun μ => ((r.2 μ : ℤ) : ℝ), fun μ => ?_, fun x μ => ?_⟩
    · rcases Int.units_eq_one_or (r.2 μ) with h | h <;> simp [h]
    · rw [SignedFrame.toMatrix_mulVec]
      rfl
end PeriodicLattice
end YangMills.Construction
