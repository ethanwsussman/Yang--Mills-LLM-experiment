import YangMills.Construction.ColdStepAtMirrorFrames.EntryBoundOfASymmetricSystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι]
theorem abs_exp_sub_sub_one_le {u v e : ℝ} (h1 : u - v ≤ e) (h2 : v - u ≤ e) :
    |Real.exp (u - v) - 1| ≤ Real.exp e - 1 := by
  rcases le_total 0 (u - v) with h | h
  · rw [abs_of_nonneg (by linarith [Real.add_one_le_exp (u - v)])]
    linarith [Real.exp_le_exp.mpr h1]
  · rw [abs_of_nonpos (by
      have := Real.exp_le_exp.mpr h
      simp only [Real.exp_zero] at this
      linarith)]
    have hb : 1 - Real.exp (u - v) ≤ Real.exp (v - u) - 1 := by
      have e1 : Real.exp (u - v) * Real.exp (v - u) = 1 := by
        rw [← Real.exp_add]
        simp
      have p1 := Real.exp_pos (u - v)
      have p2 := Real.exp_pos (v - u)
      nlinarith [sq_nonneg (Real.exp (u - v) - 1), sq_nonneg (Real.exp (v - u) - 1),
        sq_nonneg (Real.exp (u - v) - Real.exp (v - u))]
    linarith [Real.exp_le_exp.mpr h2]
theorem symmetricSystemGreenDecay_holds : SymmetricSystemGreenDecay := by
  intro ι _ _ d S lam κ hlam hκ hd0 hds hdt hS hfloor hrow x b₀ hx b
  set l : ι → ℝ := fun i => 2 * κ * d i b₀ with hl
  set y : ι → ℝ := fun i => Real.exp (l i) * x i with hy
  have hl0 : l b₀ = 0 := by simp [hl, hd0]
  have hdiff : ∀ i j, l i - l j ≤ 2 * κ * d i j := by
    intro i j
    have := hdt i j b₀
    simp only [hl]
    nlinarith
  set c : ι → ι → ℝ := fun i j => |S i j| * (Real.exp (2 * κ * d i j) - 1) with hc
  have hc0 : ∀ i j, 0 ≤ c i j := by
    intro i j
    have hdnn : 0 ≤ d i j := by
      have h1 := hdt i j i
      rw [hd0, hds j i] at h1
      linarith
    have : 1 ≤ Real.exp (2 * κ * d i j) := Real.one_le_exp (by positivity)
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hcs : ∀ i j, c i j = c j i := by
    intro i j
    simp only [hc]
    rw [hds i j, ← Matrix.IsSymm.apply hS i j]
  have hsrc : ∑ i, y i * (Real.exp (l i) * S.mulVec x i) = y b₀ := by
    rw [hx]
    simp [hl0, Pi.single_apply]
  have hexp : ∀ i, Real.exp (l i) * S.mulVec x i =
      S.mulVec y i + ∑ j, S i j * (Real.exp (l i - l j) - 1) * y j := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have e : Real.exp (l i - l j) * Real.exp (l j) = Real.exp (l i) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [hy]
    calc Real.exp (l i) * (S i j * x j)
        = S i j * ((Real.exp (l i - l j) * Real.exp (l j)) * x j) := by rw [e]; ring
      _ = _ := by ring
  have herr : ∑ i, y i * ∑ j, S i j * (Real.exp (l i - l j) - 1) * y j ≥
      -(lam / 2 * ∑ i, y i ^ 2) := by
    have hterm : ∀ i j, -(c i j * (y i ^ 2 + y j ^ 2) / 2) ≤
        y i * (S i j * (Real.exp (l i - l j) - 1) * y j) := by
      intro i j
      have hb : |S i j * (Real.exp (l i - l j) - 1)| ≤ c i j := by
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply abs_exp_sub_sub_one_le (hdiff i j)
        have := hdiff j i
        rwa [hds j i] at this
      have h1 : |y i * (S i j * (Real.exp (l i - l j) - 1) * y j)| ≤ c i j * (|y i| * |y j|) := by
        rw [show y i * (S i j * (Real.exp (l i - l j) - 1) * y j) =
          (S i j * (Real.exp (l i - l j) - 1)) * (y i * y j) by ring,
          abs_mul (S i j * (Real.exp (l i - l j) - 1)) (y i * y j), abs_mul (y i) (y j)]
        exact mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have h2 : |y i| * |y j| ≤ (y i ^ 2 + y j ^ 2) / 2 := by
        nlinarith [sq_nonneg (|y i| - |y j|), sq_abs (y i), sq_abs (y j)]
      have h3 := neg_abs_le (y i * (S i j * (Real.exp (l i - l j) - 1) * y j))
      have h4 := hc0 i j
      nlinarith
    have hsum : ∑ i, ∑ j, c i j * (y i ^ 2 + y j ^ 2) / 2 ≤ lam / 2 * ∑ i, y i ^ 2 := by
      have e1 : ∑ i, ∑ j, c i j * (y i ^ 2 + y j ^ 2) / 2 =
          ∑ i, (∑ j, c i j) * y i ^ 2 := by
        have e2 : ∑ i, ∑ j, c i j * y j ^ 2 = ∑ i, ∑ j, c i j * y i ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hcs]
        have e3 : ∀ i j, c i j * (y i ^ 2 + y j ^ 2) / 2 =
            c i j * y i ^ 2 / 2 + c i j * y j ^ 2 / 2 := fun i j => by ring
        simp only [e3, Finset.sum_add_distrib, ← Finset.sum_div]
        rw [e2]
        simp only [Finset.sum_mul]
        ring
      rw [e1, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hrow i) (by positivity)
    have : ∑ i, ∑ j, -(c i j * (y i ^ 2 + y j ^ 2) / 2) ≤
        ∑ i, y i * ∑ j, S i j * (Real.exp (l i - l j) - 1) * y j := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hterm i j
    simp only [Finset.sum_neg_distrib] at this
    linarith
  have hmain : lam / 2 * ∑ i, y i ^ 2 ≤ y b₀ := by
    have h1 := hfloor y
    have h2 : ∑ i, y i * (Real.exp (l i) * S.mulVec x i) =
        ∑ i, y i * S.mulVec y i + ∑ i, y i * ∑ j, S i j * (Real.exp (l i - l j) - 1) * y j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hexp i]
      ring
    rw [hsrc] at h2
    linarith
  set N : ℝ := ∑ i, y i ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hyi : ∀ i, y i ^ 2 ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => y i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  have hyN : N ≤ (2 / lam) ^ 2 := by
    have h1 : y b₀ ≤ Real.sqrt N := by
      apply Real.le_sqrt_of_sq_le
      exact hyi b₀
    have h2 : lam / 2 * N ≤ Real.sqrt N := hmain.trans h1
    have h3 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
    have h4 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have h5 : Real.sqrt N ≤ 2 / lam := by
      by_contra hcon
      push Not at hcon
      have h6 : 0 < Real.sqrt N := lt_of_le_of_lt (by positivity) hcon
      have h7 : lam / 2 * Real.sqrt N ≤ 1 := by
        have : lam / 2 * Real.sqrt N * Real.sqrt N ≤ 1 * Real.sqrt N := by
          nlinarith
        exact le_of_mul_le_mul_right this h6
      have h8 : 1 < lam / 2 * Real.sqrt N := by
        have : lam / 2 * (2 / lam) = 1 := by field_simp
        nlinarith
      linarith
    calc N = Real.sqrt N ^ 2 := h3.symm
      _ ≤ (2 / lam) ^ 2 := by
        apply pow_le_pow_left₀ h4 h5
  have hyb : |y b| ≤ 2 / lam := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    exact (hyi b).trans hyN
  have hxb : x b = Real.exp (-(l b)) * y b := by
    simp only [hy]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [hxb, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right hyb (Real.exp_pos _).le
end YangMills.Construction.ColdStepAtMirrorFrames
end
