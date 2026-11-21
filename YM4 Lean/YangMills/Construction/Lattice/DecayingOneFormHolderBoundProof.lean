import YangMills.Construction.Lattice.PointDecayingOneForms
import YangMills.Construction.Lattice.FieldNormProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace OneFormHolder
theorem taxicabDist_add_basisStep_le (m : Mesh N) (w : GridPoint d m) (μ : Fin d) :
    taxicabDist ((w + m.basisStep μ : GridPoint d m) : Torus d N) (w : Torus d N) ≤ m.h := by
  have e1 : ∀ ν, ‖((w + m.basisStep μ : GridPoint d m) : Torus d N) ν - (w : Torus d N) ν‖ =
      if ν = μ then ‖((m.h : ℝ) : AddCircle (N : ℝ))‖ else 0 := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp [Mesh.basisStep, axisMultiple]
    · simp [Mesh.basisStep, axisMultiple, hν]
  unfold taxicabDist
  simp only [e1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hN : (0 : ℝ) < N := by
    rw [m.period_eq]
    exact mul_pos (by exact_mod_cast m.count_pos) m.h_pos
  have e2 := round_le ((N : ℝ)⁻¹ * m.h) 0
  simp only [Int.cast_zero, sub_zero] at e2
  rw [AddCircle.norm_eq' (p := (N : ℝ)) hN]
  calc (N : ℝ) * |(N : ℝ)⁻¹ * m.h - round ((N : ℝ)⁻¹ * m.h)|
      ≤ N * |(N : ℝ)⁻¹ * m.h| := mul_le_mul_of_nonneg_left e2 hN.le
    _ = m.h := by
      rw [abs_of_pos (mul_pos (inv_pos.mpr hN) m.h_pos)]
      field_simp
end OneFormHolder
end YangMills.Construction.PeriodicLattice
