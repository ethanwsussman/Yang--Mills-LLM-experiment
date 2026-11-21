import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset Filter Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace IntegerExpSum
abbrev CircleIntPoints (N : ℕ) : Type :=
  ↥(AddSubgroup.zmultiples (((1 : ℝ)) : AddCircle (N : ℝ)))
theorem exists_int_lift (N : ℕ) (t : ℝ) (a : CircleIntPoints N) :
    ∃ n : ℤ, (((n : ℝ)) : AddCircle (N : ℝ)) = a.1 ∧
      |t - n| = ‖((t : ℝ) : AddCircle (N : ℝ)) - a.1‖ := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
  have hk : k • (((1 : ℝ)) : AddCircle (N : ℝ)) = (((k : ℝ)) : AddCircle (N : ℝ)) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_one]
  refine ⟨k + round ((N : ℝ)⁻¹ * (t - k)) * N, ?_, ?_⟩
  · have hper : (((round ((N : ℝ)⁻¹ * (t - k)) : ℝ) * (N : ℝ) : ℝ) : AddCircle (N : ℝ)) = 0 := by
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    simp only [hk]
    push_cast
    rw [AddCircle.coe_add, hper, add_zero]
  · simp only [hk]
    rw [← AddCircle.coe_sub, AddCircle.norm_eq]
    push_cast
    congr 1
    ring
end IntegerExpSum
end YangMills.Construction.PeriodicLattice
