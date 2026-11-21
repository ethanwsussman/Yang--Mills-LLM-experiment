import YangMills.Construction.CellOfTheFlow.PricesOfLongClassesAddUp
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters
private theorem le_add_of_bounded_increments {x : ℕ → ℝ} {k : ℕ} {B : ℝ} (hm : ∀ j < k, |x (j + 1) - x j| ≤ 2 * B) :
    ∀ i j : ℕ, i + j = k → x k ≤ x j + 2 * B * (i : ℝ) := by
  intro i
  induction i with
  | zero =>
    intro j h
    have : j = k := by omega
    subst this
    simp
  | succ i ih =>
    intro j h
    have h1 := ih (j + 1) (by omega)
    have h2 := (abs_le.mp (hm j (by omega))).2
    push_cast
    linarith
private theorem exponent_absorbs {u t y B i : ℝ} (hy : 0 < y) (hB : 96 * B ≤ y) (hu : y ≤ u) (hi : 1 ≤ i)
    (ht : t ≤ u + 2 * B * i) : 2 * t + y / 3 * i ≤ 25 / 8 * u * i := by
  have h1 : u ≤ u * i := by nlinarith
  have h2 : y * i ≤ u * i := by nlinarith
  have h3 : 96 * (B * i) ≤ y * i := by nlinarith
  nlinarith
private theorem geom_sum_le_one_sub_half_pow {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1 / 2) (k : ℕ) :
    ∑ i ∈ Finset.range k, q ^ (i + 1) ≤ 1 - (1 / 2 : ℝ) ^ k := by
  have hle : ∀ i : ℕ, q ^ (i + 1) ≤ (1 / 2 : ℝ) ^ (i + 1) := fun i => pow_le_pow_left₀ h0 h1 _
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have := hle k
    have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by rw [pow_succ]; ring
    rw [e] at this ⊢
    linarith
private theorem sum_exp_decay_le {a y B : ℝ} (ha : 0 < a) (hy : 0 < y) (hB : 96 * B ≤ y) (hay : 3 ≤ a * y)
    (x : ℕ → ℝ) (k : ℕ) (hx : ∀ j ≤ k, y ≤ x j) (hm : ∀ j < k, |x (j + 1) - x j| ≤ 2 * B) :
    ∑ j ∈ Finset.range k, Real.exp (-(25 / 8 * a * x j * ((k : ℝ) - j))) ≤ Real.exp (-(x k * a)) := by
  set q : ℝ := Real.exp (-(a * y / 3)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 / 2 := by
    have h1 : q ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h4 : (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
    rw [h3] at h1
    linarith
  have hterm : ∀ j ∈ Finset.range k, Real.exp (-(25 / 8 * a * x j * ((k : ℝ) - j))) ≤
      Real.exp (-(2 * a * x k)) * q ^ (k - 1 - j + 1) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hsub : k - 1 - j + 1 = k - j := by omega
    have hcast : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by
      rw [Nat.cast_sub hjk.le]
    have hi : (1 : ℝ) ≤ (k : ℝ) - j := by
      rw [← hcast]
      exact_mod_cast (by omega : 1 ≤ k - j)
    have htop := le_add_of_bounded_increments hm (k - j) j (by omega)
    rw [hcast] at htop
    have hp := exponent_absorbs hy hB (hx j hjk.le) hi htop
    rw [hsub, hq, ← Real.exp_nat_mul, ← Real.exp_add, hcast]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hp ha.le
    nlinarith
  have hsum : ∑ j ∈ Finset.range k, q ^ (k - 1 - j + 1) ≤ 1 := by
    have hr : ∑ j ∈ Finset.range k, q ^ (k - 1 - j + 1) = ∑ j ∈ Finset.range k, q ^ (j + 1) :=
      Finset.sum_range_reflect (fun i => q ^ (i + 1)) k
    rw [hr]
    have := geom_sum_le_one_sub_half_pow hq0 hq1 k
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    linarith
  have hxk : 0 ≤ x k := hy.le.trans (hx k le_rfl)
  calc ∑ j ∈ Finset.range k, Real.exp (-(25 / 8 * a * x j * ((k : ℝ) - j)))
      ≤ ∑ j ∈ Finset.range k, Real.exp (-(2 * a * x k)) * q ^ (k - 1 - j + 1) := Finset.sum_le_sum hterm
    _ = Real.exp (-(2 * a * x k)) * ∑ j ∈ Finset.range k, q ^ (k - 1 - j + 1) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(2 * a * x k)) * 1 :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ Real.exp (-(x k * a)) := by
        rw [mul_one]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg ha.le hxk]
private theorem gasRate_eq {T : ParameterAssignment} (hT : T.Admissible) :
    T.gasRate = 2⁻¹ ^ 8 * (T.κ₁ * T.threshold ^ 2) ∧ 0 < T.κ₁ * T.threshold ^ 2 := by
  have hσ : 0 < T.threshold ^ 2 := pow_pos hT.σ_pos 2
  have hκ : 0 < T.κ := hT.κ_pos
  have hE : 0 < T.cE := hT.cE_pos
  have h1 : T.κ₁ ≤ T.κ / 16 := min_le_left _ _
  have h2 : T.κ₁ ≤ T.cE / (4 * T.threshold ^ 2) := min_le_right _ _
  have hpos : 0 < T.κ₁ := lt_min (by positivity) (by positivity)
  have h3 : T.κ₁ * T.threshold ^ 2 ≤ T.κ * T.threshold ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hσ.le
  have h4 : T.κ₁ * T.threshold ^ 2 ≤ T.cE := by
    have : T.κ₁ * T.threshold ^ 2 ≤ T.cE / (4 * T.threshold ^ 2) * T.threshold ^ 2 :=
      mul_le_mul_of_nonneg_right h2 hσ.le
    have hne : T.threshold ≠ 0 := hT.σ_pos.ne'
    have e : T.cE / (4 * T.threshold ^ 2) * T.threshold ^ 2 = T.cE / 4 := by
      field_simp
    rw [e] at this
    linarith
  refine ⟨?_, mul_pos hpos hσ⟩
  unfold ParameterAssignment.gasRate
  rw [min_eq_right h3, min_eq_right h4]
theorem longSupportPriceSum : longSupportPriceSumStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hT _
  obtain ⟨hch, ha⟩ := gasRate_eq hT
  have hB : 0 < T.B := lt_of_lt_of_le one_pos hT.B_ge
  refine ⟨max (96 * T.B) (3 / (T.κ₁ * T.threshold ^ 2)), ?_⟩
  intro y hy _ _ x k hx hm
  have hy1 : 96 * T.B ≤ y := (le_max_left _ _).trans hy
  have hy2 : 3 / (T.κ₁ * T.threshold ^ 2) ≤ y := (le_max_right _ _).trans hy
  have hy0 : 0 < y := by linarith
  have hay : 3 ≤ T.κ₁ * T.threshold ^ 2 * y := by
    rw [div_le_iff₀ ha] at hy2
    linarith
  have key := sum_exp_decay_le ha hy0 hy1 hay x k hx hm
  have e : ∀ j : ℕ, 800 * T.gasRate * x j * ((k : ℝ) - j) =
      25 / 8 * (T.κ₁ * T.threshold ^ 2) * x j * ((k : ℝ) - j) := by
    intro j
    rw [hch]
    ring
  simp only [e]
  have e2 : x k * T.κ₁ * T.threshold ^ 2 = x k * (T.κ₁ * T.threshold ^ 2) := by ring
  rw [e2]
  exact key
end YangMills.Construction.CellWindows
end
