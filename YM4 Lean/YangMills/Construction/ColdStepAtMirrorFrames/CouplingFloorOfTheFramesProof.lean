import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
private lemma frameRadius_lower_bound (x : ℝ) :
    x ^ (1 / 100 : ℝ) / 2 ^ 11 - 1 ≤ (frameRadius x : ℝ) := by
  have h1 : x ^ (1 / 100 : ℝ) ≤ (⌈x ^ (1 / 100 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  set r := ⌈x ^ (1 / 100 : ℝ)⌉₊ with hr
  have h2 : r < (frameRadius x + 1) * 2 ^ 11 := by
    have : frameRadius x = r / 2 ^ 11 := rfl
    rw [this]
    have := Nat.lt_succ_iff.mpr (le_refl r)
    have h3 := Nat.div_add_mod r (2 ^ 11)
    have h4 := Nat.mod_lt r (show 0 < 2 ^ 11 by norm_num)
    nlinarith
  have h3 : (r : ℝ) ≤ ((frameRadius x : ℝ) + 1) * 2 ^ 11 := by
    exact_mod_cast h2.le
  have : x ^ (1 / 100 : ℝ) / 2 ^ 11 ≤ (frameRadius x : ℝ) + 1 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith
private lemma tendsto_rpow_hundredth : Tendsto (fun x : ℝ => x ^ (1 / 100 : ℝ)) atTop atTop :=
  tendsto_rpow_atTop (by norm_num)
private lemma tendsto_frameRadius : Tendsto (fun x : ℝ => (frameRadius x : ℝ)) atTop atTop := by
  have h : Tendsto (fun x : ℝ => x ^ (1 / 100 : ℝ) / 2 ^ 11 - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_rpow_hundredth.atTop_div_const (by norm_num))
  exact tendsto_atTop_mono frameRadius_lower_bound h
private lemma eventually_sq_mul_exp_neg_frameRadius_le_one (A c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, A * x ^ 2 * Real.exp (-(c * frameRadius x)) ≤ 1 := by
  set c' : ℝ := c / 2 ^ 11 with hc'
  have hc'pos : 0 < c' := by positivity
  have hlim : Tendsto (fun v : ℝ => v ^ 200 * Real.exp (-v)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 200
  have hv : Tendsto (fun x : ℝ => c' * x ^ (1 / 100 : ℝ)) atTop atTop :=
    tendsto_rpow_hundredth.const_mul_atTop hc'pos
  have hcomp := hlim.comp hv
  have hB : 0 < |A| * Real.exp c / c' ^ 200 + 1 := by positivity
  have hsmall : ∀ᶠ x : ℝ in atTop,
      (fun v : ℝ => v ^ 200 * Real.exp (-v)) (c' * x ^ (1 / 100 : ℝ)) <
        1 / (|A| * Real.exp c / c' ^ 200 + 1) :=
    hcomp.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_gt_atTop 0] with x hx hx0
  set u := x ^ (1 / 100 : ℝ) with hudef
  have hxu : x ^ 2 = u ^ 200 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hexp : Real.exp (-(c * frameRadius x)) ≤ Real.exp c * Real.exp (-(c' * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := frameRadius_lower_bound x
    have h2 : c * (u / 2 ^ 11 - 1) ≤ c * (frameRadius x : ℝ) :=
      mul_le_mul_of_nonneg_left this hc.le
    have h3 : c * (u / 2 ^ 11 - 1) = c' * u - c := by
      rw [hc']; ring
    linarith
  have hpow : (c' * u) ^ 200 = c' ^ 200 * u ^ 200 := mul_pow _ _ _
  replace hx : (c' * u) ^ 200 * Real.exp (-(c' * u)) <
      1 / (|A| * Real.exp c / c' ^ 200 + 1) := hx
  rw [hpow, lt_div_iff₀ hB] at hx
  have key : |A| * Real.exp c * (u ^ 200 * Real.exp (-(c' * u))) ≤ 1 := by
    have h4 : u ^ 200 * Real.exp (-(c' * u)) * (c' ^ 200 * (|A| * Real.exp c / c' ^ 200 + 1)) < 1 := by
      calc _ = c' ^ 200 * u ^ 200 * Real.exp (-(c' * u)) * (|A| * Real.exp c / c' ^ 200 + 1) := by ring
        _ < 1 := hx
    have h5 : c' ^ 200 * (|A| * Real.exp c / c' ^ 200 + 1) = |A| * Real.exp c + c' ^ 200 := by
      field_simp
    rw [h5] at h4
    have h6 : 0 ≤ u ^ 200 * Real.exp (-(c' * u)) * c' ^ 200 := by positivity
    nlinarith
  calc A * x ^ 2 * Real.exp (-(c * frameRadius x))
      ≤ |A| * x ^ 2 * Real.exp (-(c * frameRadius x)) := by
        have : 0 ≤ x ^ 2 * Real.exp (-(c * frameRadius x)) := by positivity
        nlinarith [le_abs_self A]
    _ ≤ |A| * x ^ 2 * (Real.exp c * Real.exp (-(c' * u))) := by
        apply mul_le_mul_of_nonneg_left hexp
        positivity
    _ = |A| * Real.exp c * (u ^ 200 * Real.exp (-(c' * u))) := by rw [hxu]; ring
    _ ≤ 1 := key
theorem couplingThreshold_holds : CouplingThreshold := by
  intro Cf C δ₂ κ σ N hδ hκ hκ' hσ
  have hrad : ∀ᶠ x : ℝ in atTop, ((max N 16 : ℕ) : ℝ) ≤ (frameRadius x : ℝ) :=
    tendsto_frameRadius.eventually_ge_atTop _
  have hc1 : 0 < δ₂ / 8 := by positivity
  have h1 := eventually_sq_mul_exp_neg_frameRadius_le_one (Cf / (2⁻¹ ^ 10 * σ)) (δ₂ / 4) (by positivity)
  have h2 := eventually_sq_mul_exp_neg_frameRadius_le_one (C * Cf) (δ₂ / 8) hc1
  have h3 := eventually_sq_mul_exp_neg_frameRadius_le_one C (2 * δ₂) (by positivity)
  have h4 := eventually_sq_mul_exp_neg_frameRadius_le_one Cf (δ₂ / 4) (by positivity)
  have hev := (hrad.and ((h1.and h2).and (h3.and h4))).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨y₀, hy⟩ := eventually_atTop.mp hev
  refine ⟨y₀, fun x hx => ?_⟩
  obtain ⟨⟨hr, ⟨e1, e2⟩, e3, e4⟩, hx1⟩ := hy x hx
  have hx0 : (0 : ℝ) < x := by linarith
  set m : ℕ := frameRadius x with hm
  have hmN : max N 16 ≤ m := by exact_mod_cast hr
  have hxsq : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  refine ⟨le_trans (le_max_left _ _) hmN, le_trans (le_max_right _ _) hmN, ?_, ?_, e3, ?_⟩
  · have hs : 0 < 2⁻¹ ^ 10 * σ := by positivity
    have hE : 0 ≤ Real.exp (-(δ₂ / 4 * m)) := (Real.exp_pos _).le
    by_cases hCf : Cf ≤ 0
    · have : Cf * Real.exp (-(δ₂ / 4 * m)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hCf hE
      linarith
    · have hCf' : 0 < Cf := not_le.mp hCf
      have h5 : Cf / (2⁻¹ ^ 10 * σ) * Real.exp (-(δ₂ / 4 * m)) ≤ 1 := by
        have h6 : 0 ≤ Cf / (2⁻¹ ^ 10 * σ) * Real.exp (-(δ₂ / 4 * m)) := by positivity
        nlinarith
      have h7 : Cf / (2⁻¹ ^ 10 * σ) * Real.exp (-(δ₂ / 4 * m)) =
          Cf * Real.exp (-(δ₂ / 4 * m)) / (2⁻¹ ^ 10 * σ) := by ring
      rw [h7, div_le_one hs] at h5
      exact h5
  · have hsplit : Real.exp (-(δ₂ / 4 * m)) =
        Real.exp (-(δ₂ / 8 * m)) * Real.exp (-(δ₂ / 8 * m)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle : Real.exp (-(δ₂ / 8 * m)) ≤ Real.exp (-(2 ^ 10 * κ * m)) := by
      apply Real.exp_le_exp.mpr
      have : 2 ^ 10 * κ ≤ δ₂ / 8 := by
        have : 2 ^ 10 * κ ≤ 2 ^ 10 * (δ₂ / 2 ^ 14) := by
          apply mul_le_mul_of_nonneg_left hκ' (by norm_num)
        nlinarith
      nlinarith
    have hE : 0 < Real.exp (-(δ₂ / 8 * m)) := Real.exp_pos _
    calc C * x ^ 2 * (Cf * Real.exp (-(δ₂ / 4 * m)))
        = (C * Cf * x ^ 2 * Real.exp (-(δ₂ / 8 * m))) * Real.exp (-(δ₂ / 8 * m)) := by
          rw [hsplit]; ring
      _ ≤ 1 * Real.exp (-(δ₂ / 8 * m)) := mul_le_mul_of_nonneg_right e2 hE.le
      _ ≤ Real.exp (-(2 ^ 10 * κ * m)) := by rw [one_mul]; exact hle
  · have hroot : x ^ (-(1 / 2 : ℝ)) * x ^ (2 : ℝ) = x ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    have hge : 1 ≤ x ^ (-(-(1 / 2 : ℝ))) := by
      apply Real.one_le_rpow hx1; norm_num
    have hpos : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hinv : x ^ (-(1 / 2 : ℝ)) * x ^ (-(-(1 / 2 : ℝ))) = 1 := by
      rw [← Real.rpow_add hx0]; norm_num
    have hxx : x ^ (-(-(1 / 2 : ℝ))) ≤ x ^ 2 := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hx1
      norm_num
    have hE : 0 ≤ Real.exp (-(δ₂ / 4 * m)) := (Real.exp_pos _).le
    by_cases hCf : Cf ≤ 0
    · have : Cf * Real.exp (-(δ₂ / 4 * m)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hCf hE
      linarith
    · have hCf' : 0 < Cf := not_le.mp hCf
      have h8 : Cf * Real.exp (-(δ₂ / 4 * m)) * x ^ (-(-(1 / 2 : ℝ))) ≤ 1 := by
        have hp : 0 ≤ Cf * Real.exp (-(δ₂ / 4 * m)) := by positivity
        calc Cf * Real.exp (-(δ₂ / 4 * m)) * x ^ (-(-(1 / 2 : ℝ)))
            ≤ Cf * Real.exp (-(δ₂ / 4 * m)) * x ^ 2 := mul_le_mul_of_nonneg_left hxx hp
          _ = Cf * x ^ 2 * Real.exp (-(δ₂ / 4 * m)) := by ring
          _ ≤ 1 := e4
      calc Cf * Real.exp (-(δ₂ / 4 * m))
          = Cf * Real.exp (-(δ₂ / 4 * m)) * x ^ (-(-(1 / 2 : ℝ))) * x ^ (-(1 / 2 : ℝ)) := by
            rw [mul_assoc (Cf * _), mul_comm (x ^ (-(-(1 / 2 : ℝ)))), hinv, mul_one]
        _ ≤ 1 * x ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h8 hpos.le
        _ = x ^ (-(1 / 2 : ℝ)) := one_mul _
end YangMills.Construction.ColdStepAtMirrorFrames
end
