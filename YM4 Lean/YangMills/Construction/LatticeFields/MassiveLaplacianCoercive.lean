import YangMills.Construction.LatticeFields.DirichletBlockOps
import YangMills.Construction.LatticeFields.ScaleParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def coerciveBase (d : ℕ) : ℝ := blockLapConst d + 2
def projDivBoundConst (d : ℕ) : ℝ :=
  Real.sqrt (coerciveBase d) + 2 * Real.sqrt d * coerciveBase d
def coerciveAuxConst (d : ℕ) (a : ℝ) : ℝ :=
  max (1 + 8 * (d : ℝ) * projDivBoundConst d ^ 2) (2 * projDivBoundConst d ^ 2 * a⁻¹)
def coerciveConst (d : ℕ) (a : ℝ) : ℝ := ((8 * (d : ℝ) + 1) * coerciveAuxConst d a + 2 * a⁻¹)⁻¹
end YangMills.Construction.LatticeFields
