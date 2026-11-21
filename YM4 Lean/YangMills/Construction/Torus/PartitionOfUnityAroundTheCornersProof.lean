import YangMills.Construction.Torus.ComparisonOfLocalScaledSquaresProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.VertexPartition
open Set TorusMetric
def rampClamp (s : ℝ) : ℝ := max 0 (min 1 (3 * |s| - 1))
def plateauBump (s : ℝ) : ℝ := Real.cos (Real.pi / 2 * rampClamp s)
theorem abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, f i ∈ Icc (0 : ℝ) 1) (hg : ∀ i, g i ∈ Icc (0 : ℝ) 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hQ0 : 0 ≤ ∏ k ∈ s, g k := Finset.prod_nonneg fun k _ => (hg k).1
    have hQ1 : ∏ k ∈ s, g k ≤ 1 := Finset.prod_le_one (fun k _ => (hg k).1) fun k _ => (hg k).2
    have e : f i * ∏ k ∈ s, f k - g i * ∏ k ∈ s, g k =
        f i * (∏ k ∈ s, f k - ∏ k ∈ s, g k) + (f i - g i) * ∏ k ∈ s, g k := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hf i).1, abs_of_nonneg hQ0]
    have h1 := mul_le_of_le_one_left (abs_nonneg (∏ k ∈ s, f k - ∏ k ∈ s, g k)) (hf i).2
    have h2 := mul_le_of_le_one_right (abs_nonneg (f i - g i)) hQ1
    linarith
section Circle
variable {S a : ℝ} {N : ℕ}
end Circle
section Torus
variable {S a : ℝ}
end Torus
theorem exists_side_eq_mul (D : TorusData) {j : ℕ} (hj : j ≤ D.top) :
    ∃ N : ℕ, 2 ≤ N ∧ D.side = N * D.blockSide j := by
  obtain ⟨k, hk, hS⟩ := D.side_multiple
  have hL : 3 ≤ D.L := D.blocking.three_le_factor
  refine ⟨2 * k * D.L ^ (D.top - j), ?_, ?_⟩
  · have h1 : 1 ≤ D.L ^ (D.top - j) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  · rw [hS, TorusData.blockSide, TorusData.scale]
    have e : (D.L : ℝ) ^ D.top = (D.L : ℝ) ^ (D.top - j) * (D.L : ℝ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [e]
    push_cast
    ring
theorem blockSide_pos (D : TorusData) (j : ℕ) : 0 < D.blockSide j := by apply _root_.YangMills.Construction.Weighted.LocalComparison.blockSide_pos <;> assumption
end YangMills.Construction.Weighted.VertexPartition
