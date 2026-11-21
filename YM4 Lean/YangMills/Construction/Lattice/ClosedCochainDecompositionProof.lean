import YangMills.Construction.Lattice.PeriodicLatticeForms
import Mathlib
noncomputable section
namespace YangMills.Construction.Lattice.CochainDecomposition
variable {d : ℕ}
theorem latticeInner_comm (n : ℕ) {ι : Type*} [Fintype ι] (ε : ℝ) (f g : ι → ℝ) :
    latticeInner n ε f g = latticeInner n ε g f := by
  unfold latticeInner
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end YangMills.Construction.Lattice.CochainDecomposition
