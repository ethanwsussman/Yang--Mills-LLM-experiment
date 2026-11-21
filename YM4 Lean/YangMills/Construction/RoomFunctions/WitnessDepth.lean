import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.RoomFunctions
open PeriodicLattice
structure IsSubexpGrowth (C : ℕ → ℝ) : Prop where
  mono : Monotone C
  one_le_apply : ∀ s, 1 ≤ C s
  tendsto_atTop_atTop : Tendsto C atTop atTop
  tendsto_log_div_nat : Tendsto (fun s : ℕ => Real.log (C s) / s) atTop (𝓝 0)
def scaleDepth (L : ℕ) (C : ℕ → ℝ) (d : ℝ) : ℕ := sInf {s : ℕ | C s * meshSize L s ≤ d}
section Depth
variable {L : ℕ} {C : ℕ → ℝ} {d : ℝ}
theorem meshSize_natCast_eq (L s : ℕ) : meshSize L (s : ℤ) = ((L : ℝ) ^ s)⁻¹ := by
  simp [meshSize, zpow_neg]
theorem meshSize_natCast_pos (hL : 2 ≤ L) (s : ℕ) : 0 < meshSize L (s : ℤ) := by
  have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  rw [meshSize_natCast_eq]
  positivity
theorem meshSize_natCast_anti (hL : 2 ≤ L) {s t : ℕ} (h : s ≤ t) :
    meshSize L (t : ℤ) ≤ meshSize L (s : ℤ) := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  rw [meshSize_natCast_eq, meshSize_natCast_eq]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 h)
theorem log_mul_meshSize (hL : 2 ≤ L) {x : ℝ} (hx : 0 < x) (s : ℕ) :
    Real.log (x * meshSize L (s : ℤ)) = Real.log x - s * Real.log L := by
  rw [Real.log_mul hx.ne' (meshSize_natCast_pos hL s).ne', meshSize_natCast_eq, Real.log_inv,
    Real.log_pow]
  ring
theorem log_base_pos (hL : 2 ≤ L) : 0 < Real.log L :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < L))
theorem tendsto_log_sub_mul_log (hC : IsSubexpGrowth C) (hL : 2 ≤ L) :
    Tendsto (fun s : ℕ => Real.log (C s) - s * Real.log L) atTop atBot := by
  have hl := log_base_pos hL
  have h1 : Tendsto (fun s : ℕ => Real.log (C s) / s - Real.log L) atTop (𝓝 (-Real.log L)) := by
    simpa using hC.tendsto_log_div_nat.sub_const (Real.log L)
  have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_neg (neg_lt_zero.2 hl) h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
theorem scaleDepth_set_nonempty (hC : IsSubexpGrowth C) (hL : 2 ≤ L) (hd : 0 < d) :
    {s : ℕ | C s * meshSize L s ≤ d}.Nonempty := by
  obtain ⟨s, hs⟩ := ((tendsto_log_sub_mul_log hC hL).eventually_le_atBot (Real.log d)).exists
  have hCs : 0 < C s := lt_of_lt_of_le one_pos (hC.one_le_apply s)
  refine ⟨s, ?_⟩
  have hp : 0 < C s * meshSize L (s : ℤ) := mul_pos hCs (meshSize_natCast_pos hL s)
  rw [Set.mem_ofPred_eq, ← Real.log_le_log_iff hp hd, log_mul_meshSize hL hCs]
  exact hs
theorem mul_meshSize_scaleDepth_le (hC : IsSubexpGrowth C) (hL : 2 ≤ L) (hd : 0 < d) :
    C (scaleDepth L C d) * meshSize L (scaleDepth L C d : ℕ) ≤ d :=
  Nat.sInf_mem (scaleDepth_set_nonempty hC hL hd)
theorem not_mul_meshSize_le (hC : IsSubexpGrowth C) (hL : 2 ≤ L) {S s : ℕ} (hs : s < S)
    (h : d < meshSize L ((S - 1 : ℕ) : ℤ)) : ¬ C s * meshSize L s ≤ d := by
  have h1 : meshSize L ((S - 1 : ℕ) : ℤ) ≤ meshSize L (s : ℤ) :=
    meshSize_natCast_anti hL (by omega)
  have h2 : meshSize L (s : ℤ) ≤ C s * meshSize L s :=
    le_mul_of_one_le_left (meshSize_natCast_pos hL s).le (hC.one_le_apply s)
  linarith
theorem tendsto_scaleDepth (hC : IsSubexpGrowth C) (hL : 2 ≤ L) :
    Tendsto (scaleDepth L C) (𝓝[>] 0) atTop := by
  refine tendsto_atTop.2 fun S => ?_
  filter_upwards [Ioo_mem_nhdsGT (meshSize_natCast_pos hL S)] with d hd
  by_contra hlt
  rw [not_le] at hlt
  have hS : d < meshSize L ((S + 1 - 1 : ℕ) : ℤ) := by simpa using hd.2
  exact not_mul_meshSize_le hC hL (S := S + 1) (by omega) hS
    (mul_meshSize_scaleDepth_le hC hL hd.1)
end Depth
end YangMills.Construction.RoomFunctions
end
