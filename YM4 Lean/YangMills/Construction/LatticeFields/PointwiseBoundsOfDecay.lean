import YangMills.Construction.LatticeFields.CompressedGreenDecayProof
import YangMills.Construction.LatticeFields.LocalExpBoundsOfDecayProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeFields.PointwiseOfDecay
section Generic
variable {d N : ℕ} {κ : LatticeShape d}
theorem latticeSpacing_pos [NeZero N] : 0 < latticeSpacing N := by
  have h : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact inv_pos.mpr h
end Generic
section Torus
variable (P : ScaleData) {ℓ : Fin P.d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
def pointDecayBound (c δ D : ℝ) : ℝ :=
  P.η ^ (-((P.d : ℝ) / 2)) * (c * Real.exp ((2 * (P.d : ℝ) + 1) * δ) * Real.exp (-δ * D))
theorem eta_pos : 0 < P.η := latticeSpacing_pos
def supToL2Factor : ℝ := (P.d : ℝ) * 2 ^ ((P.d : ℝ) / 2)
theorem decayConst_eq (c δ D : ℝ) :
    secondOrderDecayConst P.d c δ * P.η ^ (-((P.d : ℝ) / 2 + 1)) * Real.exp (-δ * D) =
      2 * (P.d : ℝ) * P.η⁻¹ * (pointDecayBound P c δ D * supToL2Factor P) := by
  have hη := eta_pos P
  have h : P.η ^ (-((P.d : ℝ) / 2 + 1)) = P.η⁻¹ * P.η ^ (-((P.d : ℝ) / 2)) := by
    rw [neg_add, Real.rpow_add hη, Real.rpow_neg_one]
    ring
  rw [h]
  unfold secondOrderDecayConst pointDecayBound supToL2Factor
  ring
end Torus
end YangMills.Construction.LatticeFields.PointwiseOfDecay
