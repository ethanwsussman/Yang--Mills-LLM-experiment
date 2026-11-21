import YangMills.Construction.Lattice.PropagatorBoundsOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.PropagatorConstants
structure IsPropagatorConstants (L : ℕ) (B δ a : ℝ) (r : ℕ) : Prop where
  one_le_bound : 1 ≤ B
  rate_pos : 0 < δ
  rate_le_one : δ ≤ 1
  smallness_pos : 0 < a
  smallness_le : a ≤ straightenedCurvatureThreshold L
  radius_eq_pow : ∃ n : ℕ, r = L ^ n
  le_radius : L ≤ r
  bounds : GlobalPropagatorBounds L B δ a r
def constants (L : ℕ) : ℝ × ℝ × ℝ × ℕ :=
  Classical.epsilon fun t => IsPropagatorConstants L t.1 t.2.1 t.2.2.1 t.2.2.2
def radius (L : ℕ) : ℕ := (constants L).2.2.2
end YangMills.Construction.PeriodicLattice.PropagatorConstants
end
