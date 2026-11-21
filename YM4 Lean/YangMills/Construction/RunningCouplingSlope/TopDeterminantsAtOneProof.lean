import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Matrix Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace DeterminantsAtTrivialField
section BlockDeterminants
variable {I T : Type} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
private theorem det_blocks_reassoc (Ξ : Matrix I I ℂ) (Bu B : Matrix T I ℂ) (But Bt : Matrix I T ℂ)
    (G : Matrix T T ℂ) :
    det (fromBlocks (fromBlocks Ξ But Bu (-G)) (fromRows Bt 0) (fromCols B 0) (1 : Matrix T T ℂ)) =
      det (fromBlocks Ξ (fromCols But Bt) (fromRows Bu B) (fromBlocks (-G) 0 0 (1 : Matrix T T ℂ))) := by
  rw [← det_submatrix_equiv_self (Equiv.sumAssoc I T T).symm
    (fromBlocks (fromBlocks Ξ But Bu (-G)) (fromRows Bt 0) (fromCols B 0) (1 : Matrix T T ℂ))]
  congr 1
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;> simp
private theorem det_mixedSaddle_eq (Ξ : Matrix I I ℂ) (Bu B : Matrix T I ℂ) (But Bt : Matrix I T ℂ)
    (G : Matrix T T ℂ) (hΞ : det Ξ ≠ 0) :
    det (fromBlocks (Ξ - Bt * B) But Bu (-G)) =
      det Ξ * det (fromBlocks (-G - Bu * Ξ⁻¹ * But) (-(Bu * Ξ⁻¹ * Bt)) (-(B * Ξ⁻¹ * But))
        (1 - B * Ξ⁻¹ * Bt)) := by
  have hu : IsUnit (det Ξ) := isUnit_iff_ne_zero.2 hΞ
  let _ : Invertible Ξ := invertibleOfIsUnitDet Ξ hu
  have e1 : det (fromBlocks (fromBlocks Ξ But Bu (-G)) (fromRows Bt 0) (fromCols B 0)
      (1 : Matrix T T ℂ)) = det (fromBlocks (Ξ - Bt * B) But Bu (-G)) := by
    let _ : Invertible (1 : Matrix T T ℂ) := invertibleOne
    rw [det_fromBlocks₂₂]
    simp only [invOf_one, det_one, one_mul, mul_one]
    congr 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type]
  rw [← e1, det_blocks_reassoc, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 2
  rw [fromRows_mul, fromRows_mul_fromCols]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [sub_eq_add_neg]
abbrev _root_.YangMills.SharedProofs.p321 := @det_mixedSaddle_eq
private theorem det_saddle_eq (Ξ : Matrix I I ℂ) (B : Matrix T I ℂ) (Bt : Matrix I T ℂ)
    (hΞ : det Ξ ≠ 0) :
    det (fromBlocks (Ξ - Bt * B) Bt B (0 : Matrix T T ℂ)) = det Ξ * det (-(B * Ξ⁻¹ * Bt)) := by
  have hu : IsUnit (det Ξ) := isUnit_iff_ne_zero.2 hΞ
  let _ : Invertible Ξ := invertibleOfIsUnitDet Ξ hu
  have e : fromBlocks (Ξ - Bt * B) Bt B (0 : Matrix T T ℂ) * fromBlocks 1 0 B 1 =
      fromBlocks Ξ Bt B 0 := by
    rw [fromBlocks_multiply]
    simp
  have d : det (fromBlocks (1 : Matrix I I ℂ) 0 B (1 : Matrix T T ℂ)) = 1 := by
    rw [det_fromBlocks_zero₁₂]
    simp
  have := congrArg det e
  rw [det_mul, d, mul_one] at this
  rw [this, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  simp
abbrev _root_.YangMills.SharedProofs.p73231 := @det_saddle_eq
private theorem det_twoMapSaddle_eq (Δ : Matrix I I ℂ) (Cu C : Matrix T I ℂ) (Ct : Matrix I T ℂ)
    (hΔ : det (Δ + Ct * C) ≠ 0) :
    det (fromBlocks Δ Ct Cu (0 : Matrix T T ℂ)) =
      det (Δ + Ct * C) * det (-(Cu * (Δ + Ct * C)⁻¹ * Ct)) := by
  have hu : IsUnit (det (Δ + Ct * C)) := isUnit_iff_ne_zero.2 hΔ
  let _ : Invertible (Δ + Ct * C) := invertibleOfIsUnitDet _ hu
  have e : fromBlocks Δ Ct Cu (0 : Matrix T T ℂ) * fromBlocks 1 0 C 1 =
      fromBlocks (Δ + Ct * C) Ct Cu 0 := by
    rw [fromBlocks_multiply]
    simp
  have d : det (fromBlocks (1 : Matrix I I ℂ) 0 C (1 : Matrix T T ℂ)) = 1 := by
    rw [det_fromBlocks_zero₁₂]
    simp
  have := congrArg det e
  rw [det_mul, d, mul_one] at this
  rw [this, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  simp
abbrev _root_.YangMills.SharedProofs.p13006 := @det_twoMapSaddle_eq
end BlockDeterminants
end DeterminantsAtTrivialField
end YangMills.Construction.RunningCouplingSlope
end
