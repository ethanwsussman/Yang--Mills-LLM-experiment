import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.Lattice.GaugeTermOnACubeProof
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace CellCubeSumBounds
theorem exists_lift_abs_eq_norm (p : ℝ) (c : AddCircle p) :
    ∃ r : ℝ, (r : AddCircle p) = c ∧ |r| = ‖c‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem card_Icc_ceil_floor_le (a : ℝ) (M : ℕ) :
    (Icc ⌈(a - 1) * M⌉ ⌊(a + 1) * M⌋).card ≤ 2 * M + 1 := by
  have h : (a + 1) * M = (a - 1) * M + ((2 * M : ℕ) : ℝ) := by
    push_cast
    ring
  rw [Int.card_Icc, h, Int.floor_add_natCast]
  have := Int.floor_le_ceil ((a - 1) * (M : ℝ))
  push_cast
  omega
section Cells
variable {L j : ℕ} (S : Scales d L j N)
theorem fineScale_pos (S : Scales d L j N) : 0 < fineScale L j := S.fineMesh.h_pos
end Cells
end CellCubeSumBounds
end YangMills.Construction.PeriodicLattice
