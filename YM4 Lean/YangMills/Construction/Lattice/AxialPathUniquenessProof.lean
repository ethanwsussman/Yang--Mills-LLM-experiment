import YangMills.Construction.Lattice.AxialPathUniqueness
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
namespace AxialUniqueness
variable {L m : ℕ} {j : ℤ}
theorem zsmul_unitStep_apply (n : ℤ) (μ ν : Fin 4) :
    ((n • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      if ν = μ then (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) else 0 := by
  have h1 : ((n • unitStep L m j μ : Site L m j) : FourTorus L m) =
      n • pointOnAxis L m μ (meshSize L j) := rfl
  rw [h1, Pi.smul_apply]
  by_cases h : ν = μ
  · subst h
    simp [pointOnAxis]
  · simp [pointOnAxis, h]
theorem int_eq_zero_of_mul_meshSize_coe_eq_zero (hL : 0 < L) (d : ℤ)
    (h : (((d : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0)
    (hd : |(d : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j)) : d = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.int_eq_zero_of_coe_mul_meshSize <;> assumption
theorem int_eq_zero_of_zsmul_unitStep_eq_zero (hL : 0 < L) (μ : Fin 4) (d : ℤ)
    (h : d • unitStep L m j μ = 0) (hd : |(d : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j)) : d = 0 := by
  refine int_eq_zero_of_mul_meshSize_coe_eq_zero (m := m) (j := j) hL d ?_ hd
  have h1 := zsmul_unitStep_apply (L := L) (m := m) (j := j) d μ μ
  rw [h] at h1
  simpa using h1.symm
theorem flowAlong_eq_of_axial (hL : 0 < L) {x x' : Site L m j} {μ μ' : Fin 4} {n n' : ℤ}
    (h : IsAxialDisplacement x x' μ n) (h' : IsAxialDisplacement x x' μ' n') :
    flowAlong x μ n = flowAlong x μ' n' := by
  obtain ⟨e, b⟩ := h
  obtain ⟨e', b'⟩ := h'
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hP : (0 : ℝ) < (L : ℝ) ^ ((m : ℤ) + j) := zpow_pos hL' _
  have b1 : |(n : ℝ)| < (L : ℝ) ^ ((m : ℤ) + j) := by simpa using b
  have b2 : |(n' : ℝ)| < (L : ℝ) ^ ((m : ℤ) + j) := by simpa using b'
  have heq : n • unitStep L m j μ = n' • unitStep L m j μ' := e.symm.trans e'
  by_cases hμ : μ = μ'
  · subst hμ
    have hz : (n - n') • unitStep L m j μ = 0 := by rw [sub_zsmul, heq, add_neg_cancel]
    have hd : |((n - n' : ℤ) : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j) := by
      push_cast
      have := abs_sub (n : ℝ) (n' : ℝ)
      linarith
    have := int_eq_zero_of_zsmul_unitStep_eq_zero hL μ (n - n') hz hd
    have hn : n = n' := by omega
    rw [hn]
  · have c1 := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) heq
    have c2 := congrArg (fun s : Site L m j => (s : FourTorus L m) μ') heq
    simp only [zsmul_unitStep_apply, if_true, if_neg hμ, if_neg (Ne.symm hμ)] at c1 c2
    have hn : n = 0 := int_eq_zero_of_mul_meshSize_coe_eq_zero (m := m) (j := j) hL n c1
      (by linarith)
    have hn' : n' = 0 := int_eq_zero_of_mul_meshSize_coe_eq_zero (m := m) (j := j) hL n'
      c2.symm (by linarith)
    subst hn hn'
    simp [flowAlong, forwardAxisPath]
end AxialUniqueness
open AxialUniqueness in
theorem axialPathUniqueness_holds : AxialPathUniqueness := by
  intro L m hL _ j _ x x' μ μ' n n' h h'
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨flowAlong_eq_of_axial hL0 h h', ?_⟩
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  rw [axialPath, dif_pos hex]
  exact flowAlong_eq_of_axial hL0 hex.choose_spec h
end YangMills.Construction.PeriodicLattice
