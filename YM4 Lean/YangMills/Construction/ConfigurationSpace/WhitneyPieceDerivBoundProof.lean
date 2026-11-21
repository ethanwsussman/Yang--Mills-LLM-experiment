import YangMills.Construction.ConfigurationSpace.BlockProdDerivBound
import YangMills.Construction.ConfigurationSpace.DiagonalCutoffBounds
import YangMills.Construction.ConfigurationSpace.IterDirDerivLeibniz
import YangMills.Construction.ConfigurationSpace.WhitneyPieceDerivBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.WhitneyPieceDeriv
open YangMills.Construction.BumpFunctions YangMills.Construction.WhitneyScales
open scoped ContDiff
section MultiIndices
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem sum_choose_eq_two_pow (γ : MultiIdx I) :
    ∑ γ' ∈ Fintype.piFinset (fun ι => Finset.range (γ ι + 1)), MultiIdx.choose γ γ' =
      2 ^ MultiIdx.order γ := by
  simp only [MultiIdx.choose, MultiIdx.order]
  rw [← Finset.prod_univ_sum (fun ι => Finset.range (γ ι + 1)) (fun ι k => (γ ι).choose k)]
  simp only [Nat.sum_range_choose]
  rw [Finset.prod_pow_eq_pow_sum]
theorem order_add_order_sub {γ γ' : MultiIdx I}
    (h : γ' ∈ Fintype.piFinset (fun ι => Finset.range (γ ι + 1))) :
    MultiIdx.order γ' + MultiIdx.order (γ - γ') = MultiIdx.order γ := by
  simp only [MultiIdx.order, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  have hι := Finset.mem_range.mp (Fintype.mem_piFinset.mp h ι)
  simp only [Pi.sub_apply]
  omega
end MultiIndices
theorem factorial_sq_mul_factorial_sq_le (a b : ℕ) :
    (a.factorial : ℝ) ^ 2 * (b.factorial : ℝ) ^ 2 ≤ ((a + b).factorial : ℝ) ^ 2 := by
  have h : a.factorial * b.factorial ≤ (a + b).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a b)
  have hr : (a.factorial : ℝ) * b.factorial ≤ ((a + b).factorial : ℝ) := by exact_mod_cast h
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hr 2
theorem ofRealFun_shellDiff_mem_smoothSet (hF : DiagonalCutoffProperties)
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ofRealFun (shellDiff (n := n) j) ∈ smoothSet (Config n) := by
  cases j with
  | zero => exact (hF n hn 0).2.1.1
  | succ j =>
    have h1 : ContDiff ℝ ∞ (ofRealFun (pairCutoffProd (n := n) (j + 1))) :=
      (hF n hn (j + 1)).2.1.1
    have h0 : ContDiff ℝ ∞ (ofRealFun (pairCutoffProd (n := n) j)) := (hF n hn j).2.1.1
    have he : ofRealFun (shellDiff (n := n) (j + 1)) =
        fun x => ofRealFun (pairCutoffProd (j + 1)) x - ofRealFun (pairCutoffProd j) x := by
      funext x
      simp [ofRealFun, shellDiff]
    rw [he]
    exact h1.sub h0
theorem max_pairCutoffConst_nonneg :
    0 ≤ max pairCutoffConst (2 * blockConst * whitneyRatio⁻¹) := by
  have hc : 0 < whitneyRatio := isWhitneyRatio_whitneyRatio.1
  have hb : 0 ≤ blockConst := by norm_num [blockConst, gevreyConst]
  exact le_max_of_le_right (by positivity)
theorem leibniz_term_le (n j a b : ℕ) (hn : 1 ≤ n) :
    2 * (pairCutoffConst * n * 2 ^ j) ^ a * (a.factorial : ℝ) ^ 2 *
      (integralConstBound ^ (4 * n) * (2 * blockConst * whitneyRatio⁻¹ * 2 ^ j) ^ b *
        (b.factorial : ℝ) ^ 2) ≤
    2 * integralConstBound ^ (4 * n) *
      (max pairCutoffConst (2 * blockConst * whitneyRatio⁻¹) * n * 2 ^ j) ^ (a + b) *
      ((a + b).factorial : ℝ) ^ 2 := by
  have hc : 0 < whitneyRatio := isWhitneyRatio_whitneyRatio.1
  have hb : 0 ≤ blockConst := by norm_num [blockConst, gevreyConst]
  have hA : 0 ≤ integralConstBound := zero_le_one.trans (le_max_left _ _)
  have hH : 0 ≤ pairCutoffConst := by
    unfold pairCutoffConst
    positivity
  have hM := max_pairCutoffConst_nonneg
  set M := max pairCutoffConst (2 * blockConst * whitneyRatio⁻¹) with hMdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : (pairCutoffConst * n * 2 ^ j) ^ a ≤ (M * n * 2 ^ j) ^ a := by
    refine pow_le_pow_left₀ (by positivity) ?_ a
    have : pairCutoffConst ≤ M := le_max_left _ _
    gcongr
  have h3 : (2 * blockConst * whitneyRatio⁻¹ * 2 ^ j) ^ b ≤ (M * n * 2 ^ j) ^ b := by
    refine pow_le_pow_left₀ (by positivity) ?_ b
    have hD : 2 * blockConst * whitneyRatio⁻¹ ≤ M := le_max_right _ _
    have hMn : M ≤ M * n := le_mul_of_one_le_right hM hn'
    exact mul_le_mul_of_nonneg_right (hD.trans hMn) h2.le
  have hf := factorial_sq_mul_factorial_sq_le a b
  calc 2 * (pairCutoffConst * n * 2 ^ j) ^ a * (a.factorial : ℝ) ^ 2 *
        (integralConstBound ^ (4 * n) * (2 * blockConst * whitneyRatio⁻¹ * 2 ^ j) ^ b *
          (b.factorial : ℝ) ^ 2)
      ≤ 2 * (M * n * 2 ^ j) ^ a * (a.factorial : ℝ) ^ 2 *
        (integralConstBound ^ (4 * n) * (M * n * 2 ^ j) ^ b * (b.factorial : ℝ) ^ 2) := by
        gcongr
    _ = 2 * integralConstBound ^ (4 * n) * (M * n * 2 ^ j) ^ (a + b) *
        ((a.factorial : ℝ) ^ 2 * (b.factorial : ℝ) ^ 2) := by
        rw [pow_add]
        ring
    _ ≤ 2 * integralConstBound ^ (4 * n) * (M * n * 2 ^ j) ^ (a + b) *
        ((a + b).factorial : ℝ) ^ 2 := by
        gcongr
theorem whitneyPieceDerivBound_of_cutoffs (hF : DiagonalCutoffProperties)
    (hL : IterDirDerivLeibniz)
    (hB : BlockProdDerivBound) : WhitneyPieceDerivBound := by
  intro n hn j z γ x
  have hf := ofRealFun_shellDiff_mem_smoothSet hF n hn j
  obtain ⟨hb, hbb⟩ := hB n hn j z
  obtain ⟨-, -, -, -, -, -, -, -, hfb⟩ := (hF n hn j).2.2
  have hprod : ofRealFun (whitneyPiece j z) =
      fun y => ofRealFun (shellDiff j) y * ofRealFun (blockProd j z) y := by
    funext y
    simp [ofRealFun, whitneyPiece]
  set K : ℝ := 2 * integralConstBound ^ (4 * n) *
      (max pairCutoffConst (2 * blockConst * whitneyRatio⁻¹) * n * 2 ^ j) ^
        MultiIdx.order γ * ((MultiIdx.order γ).factorial : ℝ) ^ 2 with hK
  have hsum : ‖configMultiDeriv γ (ofRealFun (whitneyPiece j z)) x‖ ≤
      ∑ γ' ∈ Fintype.piFinset (fun ι => Finset.range (γ ι + 1)),
        (MultiIdx.choose γ γ' : ℝ) * K := by
    unfold configMultiDeriv
    rw [hprod, hL (Config n) (CoordIndex n) coordBasis γ _ hf _ hb x]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ' hγ' => ?_)
    rw [norm_mul, norm_mul, Complex.norm_natCast, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 := hfb γ' x
    have h2 := hbb (γ - γ') x
    have hs := order_add_order_sub hγ'
    have ht := leibniz_term_le n j (MultiIdx.order γ') (MultiIdx.order (γ - γ')) hn
    rw [hs] at ht
    refine (mul_le_mul h1 h2 (norm_nonneg _) ?_).trans ht
    have hH : 0 ≤ pairCutoffConst := by
      have hb0 : 0 ≤ blockConst := by norm_num [blockConst, gevreyConst]
      have hA : 0 ≤ integralConstBound := zero_le_one.trans (le_max_left _ _)
      unfold pairCutoffConst
      positivity
    positivity
  refine hsum.trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_choose_eq_two_pow, hK]
  unfold pieceDerivBound pieceDerivConst
  rw [pow_mul' (2 : ℝ) j (MultiIdx.order γ)]
  push_cast
  rw [show 2 * max pairCutoffConst (2 * blockConst * whitneyRatio⁻¹) * (n : ℝ) =
    2 * (max pairCutoffConst (2 * blockConst * whitneyRatio⁻¹) * n) by ring]
  rw [mul_pow, mul_pow, mul_pow]
  ring
end YangMills.Construction.ConfigurationSpace.WhitneyPieceDeriv
end
