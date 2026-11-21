import YangMills.Construction.BumpFunctions.ExpNegInvIntegralBounds
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.BumpFunctions
theorem expNegInvIntegralBounds : ExpNegInvIntegralBounds := by
  have hglue : expNegInv = expNegInvGlue := by
    funext t
    unfold expNegInv expNegInvGlue
    by_cases h : 0 < t
    · rw [if_pos h, if_neg (not_le.mpr h), neg_div, one_div]
    · rw [if_neg h, if_pos (not_lt.mp h)]
  have hcont : Continuous expNegInv := by
    rw [hglue]
    exact (expNegInvGlue.contDiff (n := 0)).continuous
  have hnonneg : ∀ t, 0 ≤ expNegInv t := fun t => by
    rw [hglue]
    exact expNegInvGlue.nonneg t
  have hleOne : ∀ t, expNegInv t ≤ 1 := by
    intro t
    unfold expNegInv
    split_ifs with h
    · exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) h.le)
    · exact zero_le_one
  have hvanish : ∀ t, t ≤ 0 → expNegInv t = 0 := fun t h => if_neg (not_lt.mpr h)
  have hposIff : ∀ t, 0 < expNegInv t ↔ 0 < t := by
    intro t
    constructor
    · intro h
      by_contra hn
      rw [hvanish t (not_lt.mp hn)] at h
      exact lt_irrefl 0 h
    · intro h
      rw [hglue]
      exact expNegInvGlue.pos_of_pos h
  have hmulIcc : ∀ a b, expNegInv a * expNegInv b ∈ Icc (0 : ℝ) 1 := fun a b =>
    ⟨mul_nonneg (hnonneg a) (hnonneg b), mul_le_one₀ (hleOne a) (hnonneg b) (hleOne b)⟩
  have hcontFirst : Continuous (fun τ : ℝ => expNegInv τ * expNegInv (1 - τ)) :=
    hcont.mul (hcont.comp (continuous_const.sub continuous_id))
  have hcontSecond : Continuous (fun t : ℝ => expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)) :=
    (hcont.comp (continuous_id.add continuous_const)).mul
      (hcont.comp (continuous_const.sub continuous_id))
  have hposFirst : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 < expNegInv τ * expNegInv (1 - τ) := fun τ h =>
    mul_pos ((hposIff _).2 h.1) ((hposIff _).2 (sub_pos.2 h.2))
  have hzeroFirst : ∀ τ : ℝ, τ ∉ Ioo (0 : ℝ) 1 → expNegInv τ * expNegInv (1 - τ) = 0 := by
    intro τ h
    by_cases h0 : 0 < τ
    · have h1 : 1 ≤ τ := by
        by_contra h1
        exact h ⟨h0, not_le.mp h1⟩
      rw [hvanish (1 - τ) (by linarith), mul_zero]
    · rw [hvanish τ (not_lt.mp h0), zero_mul]
  have hposSecond : ∀ t ∈ Ioo (-(1 / 4) : ℝ) (1 / 4),
      0 < expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t) := fun t h =>
    mul_pos ((hposIff _).2 (by linarith [h.1])) ((hposIff _).2 (by linarith [h.2]))
  have hzeroSecond : ∀ t : ℝ, t ∉ Ioo (-(1 / 4) : ℝ) (1 / 4) →
      expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t) = 0 := by
    intro t h
    by_cases h0 : -(1 / 4) < t
    · have h1 : 1 / 4 ≤ t := by
        by_contra h1
        exact h ⟨h0, not_le.mp h1⟩
      rw [hvanish (1 / 4 - t) (by linarith), mul_zero]
    · rw [hvanish (t + 1 / 4) (by linarith [not_lt.mp h0]), zero_mul]
  refine ⟨⟨hcont, fun t => ⟨hnonneg t, hleOne t⟩, hposIff⟩,
    ⟨hcontFirst, hcontSecond, fun τ => hmulIcc _ _, fun t => hmulIcc _ _, hposFirst, hzeroFirst,
      hposSecond, hzeroSecond⟩, ?_, ?_, ?_⟩
  · intro t₁ h0 h1
    constructor
    · exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcontFirst.intervalIntegrable _ _)
        (fun x hx => hposFirst x ⟨hx.1, hx.2.trans_le h1⟩) h0
    · calc ∫ τ in (0 : ℝ)..t₁, expNegInv τ * expNegInv (1 - τ)
          ≤ ∫ _τ in (0 : ℝ)..t₁, (1 : ℝ) :=
            intervalIntegral.integral_mono_on h0.le (hcontFirst.intervalIntegrable _ _)
              (continuous_const.intervalIntegrable _ _) (fun x _ => (hmulIcc _ _).2)
        _ = t₁ := by simp
        _ ≤ 1 := h1
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcontSecond.intervalIntegrable _ _)
      hposSecond (by norm_num)
  · calc ∫ t in (-(1 / 4) : ℝ)..(1 / 4), expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)
        ≤ ∫ _t in (-(1 / 4) : ℝ)..(1 / 4), (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by norm_num) (hcontSecond.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _) (fun x _ => (hmulIcc _ _).2)
      _ = 1 / 2 := by
          rw [intervalIntegral.integral_const]
          norm_num
end YangMills.Construction.BumpFunctions
