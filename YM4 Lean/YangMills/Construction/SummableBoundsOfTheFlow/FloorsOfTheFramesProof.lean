import YangMills.Construction.SummableBoundsOfTheFlow.FloorsOfTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames Filter Topology
namespace YangMills.Construction.Estimates
private theorem rpow_div_le_frameRadius {x : ℝ} (hx : 1 ≤ x) (h : (2 : ℝ) ^ 12 ≤ x ^ (1 / 100 : ℝ)) :
    x ^ (1 / 100 : ℝ) / 2 ^ 12 ≤ frameRadius x := by
  set u := x ^ (1 / 100 : ℝ) with hu
  have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
  have h2 : ((⌈u⌉₊ / 2 ^ 11 : ℕ) : ℝ) + 1 ≥ (⌈u⌉₊ : ℝ) / 2 ^ 11 := by
    have := Nat.lt_div_mul_add (a := ⌈u⌉₊) (b := 2 ^ 11) (by norm_num)
    have h3 : (⌈u⌉₊ : ℝ) < ((⌈u⌉₊ / 2 ^ 11 : ℕ) : ℝ) * 2 ^ 11 + 2 ^ 11 := by exact_mod_cast this
    rw [ge_iff_le, div_le_iff₀ (by norm_num)]
    nlinarith
  show u / 2 ^ 12 ≤ ((⌈u⌉₊ / 2 ^ 11 : ℕ) : ℝ)
  have h5 : (1 : ℝ) ≤ u / 2 ^ 12 := by rw [le_div_iff₀ (by norm_num)]; linarith
  linarith
theorem frameRadiusGrowth : frameRadiusGrowthStatement := by
  intro A c hA hc
  set c' : ℝ := c / 2 ^ 12 with hc'
  have hc'0 : 0 < c' := by positivity
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 200
  have ht2 : Tendsto (fun u : ℝ => (c' * u) ^ 200 * Real.exp (-(c' * u))) atTop (𝓝 0) :=
    ht.comp (tendsto_id.const_mul_atTop hc'0)
  have hev := (ht2.eventually (gt_mem_nhds (show (0 : ℝ) < c' ^ 200 / A by positivity)))
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 hev
  set U : ℝ := max (max u₀ ((2 : ℝ) ^ 12)) (A * 2 ^ 12) with hU
  have hU1 : (1 : ℝ) ≤ U := le_trans (by norm_num) ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨U ^ (100 : ℕ), one_le_pow₀ hU1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (one_le_pow₀ hU1).trans hx
  have hx0 : 0 < x := by linarith
  set u := x ^ (1 / 100 : ℝ) with hu
  have hu_pow : u ^ (100 : ℕ) = x := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have hUu : U ≤ u := by
    by_contra hlt
    push_neg at hlt
    have := pow_lt_pow_left₀ hlt hu0.le (n := 100) (by norm_num)
    rw [hu_pow] at this
    linarith
  have hr := rpow_div_le_frameRadius hx1 ((((le_max_right _ _).trans (le_max_left _ _)).trans hUu))
  have hm : u / 2 ^ 12 ≤ frameRadius x := hr
  constructor
  · have h1 := hu₀ u (((le_max_left _ _).trans (le_max_left _ _)).trans hUu)
    have hx2 : x ^ 2 = u ^ 200 := by rw [← hu_pow]; ring
    have h2 : Real.exp (-(c * frameRadius x)) ≤ Real.exp (-(c' * u)) := by
      apply Real.exp_le_exp.2
      have : c' * u = c * (u / 2 ^ 12) := by rw [hc']; ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hm hc.le
      linarith
    have h3 : (c' * u) ^ 200 * Real.exp (-(c' * u)) = c' ^ 200 * (u ^ 200 * Real.exp (-(c' * u))) := by
      rw [mul_pow]; ring
    rw [h3] at h1
    have h4 : u ^ 200 * Real.exp (-(c' * u)) < 1 / A := by
      have : c' ^ 200 * (u ^ 200 * Real.exp (-(c' * u))) < c' ^ 200 * (1 / A) := by
        calc _ < c' ^ 200 / A := h1
          _ = _ := by ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    rw [hx2]
    calc A * u ^ 200 * Real.exp (-(c * frameRadius x))
        ≤ A * u ^ 200 * Real.exp (-(c' * u)) := by gcongr
      _ = A * (u ^ 200 * Real.exp (-(c' * u))) := by ring
      _ ≤ A * (1 / A) := by gcongr
      _ = 1 := by field_simp
  · have : A * 2 ^ 12 ≤ u := (le_max_right _ _).trans hUu
    have h5 : A ≤ u / 2 ^ 12 := by rw [le_div_iff₀ (by norm_num)]; exact this
    linarith
end YangMills.Construction.Estimates
end
