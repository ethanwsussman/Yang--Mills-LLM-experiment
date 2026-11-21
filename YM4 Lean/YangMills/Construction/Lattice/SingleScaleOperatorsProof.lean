import YangMills.Construction.Lattice.DifferenceOperatorsCellAveragesTrees
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace SingleScaleOps
theorem mesh_ext {s s' : Mesh N} (h : s.h = s'.h) (p : s.count = s'.count) : s = s' := by
  cases s
  cases s'
  simp_all
def oneFormRestrict {s s' : Mesh N} (hle : gridSubgroup d s' ≤ gridSubgroup d s) :
    OneForm d s →ₗ[ℝ] OneForm d s' where
  toFun A := ofMap fun b => A (b.1, AddSubgroup.inclusion hle b.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem inner_apply_eq_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hidem : ∀ f, T (T f) = T f) (f : E) :
    inner ℝ f (T f) = ‖T f‖ ^ 2 := by
  rw [← hidem f, ← hT f, hidem f, real_inner_self_eq_norm_sq]
variable {L j : ℕ}
end SingleScaleOps
end YangMills.Construction.PeriodicLattice
