import YangMills.Construction.Conventions.SignedConjugate
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
structure CheckerboardDatum (L : ℕ) where
  depth : ℕ
  sizeExp : ℕ
  cellExp : ℤ
  basePoint : Fin 4 → ℝ
  one_le_depth_add_sizeExp : 1 ≤ depth + sizeExp
  neg_depth_le_cellExp : -(depth : ℤ) ≤ cellExp
  cellExp_le_sizeExp : cellExp ≤ (sizeExp : ℤ)
  basePoint_mem : ∀ μ, ∃ i : ℤ, basePoint μ = PeriodicLattice.meshSize L (depth : ℤ) * ((i : ℝ) + 1 / 2)
namespace CheckerboardDatum
variable {L : ℕ}
def spacing (q : CheckerboardDatum L) : ℝ := PeriodicLattice.meshSize L (q.depth : ℤ)
def IsNormalized (q : CheckerboardDatum L) : Prop :=
  1 ≤ q.depth ∧ 1 ≤ q.sizeExp ∧ 0 ≤ q.cellExp ∧
    q.basePoint = (-(1 / 2) * q.spacing) • Conventions.onesVector
end CheckerboardDatum
end YangMills.Construction.ReflectionPositivity
