import YangMills.Construction.LatticeFields.BondCompressionBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d N : ℕ} {κ : LatticeShape d}
def secondOrderDecayConst (d : ℕ) (c δ : ℝ) : ℝ :=
  2 * (d : ℝ) ^ 2 * c * (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((2 * (d : ℝ) + 1) * δ)
end YangMills.Construction.LatticeFields
