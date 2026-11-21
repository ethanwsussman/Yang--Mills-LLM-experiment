import YangMills.Construction.ParameterData.FirstPassageOfTheFlow
import YangMills.Construction.ParameterData.TheCouplingAlongTheLine
import YangMills.Construction.ParameterData.TheCouplingAtADistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open Filter Topology
private lemma tendsto_log_affine_div (C b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.log (C + b * t) / t) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun w : ℝ => Real.log w ^ 1 / (b⁻¹ * w + (-(C * b⁻¹)))) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop _ _ 1 (inv_ne_zero hb.ne')
  have h₂ : Tendsto (fun t : ℝ => C + b * t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hb)
  refine (h₁.comp h₂).congr (fun t => ?_)
  have : b⁻¹ * (C + b * t) + -(C * b⁻¹) = t := by
    field_simp
    ring
  simp only [Function.comp, pow_one, this]
private lemma exists_mul_log_affine_le_half (C b lg p : ℝ) (hb : 0 < b) (hlg : 0 < lg) (hp : 0 ≤ p) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ t, M₀ ≤ t → p * Real.log (C + b * t) ≤ lg * t / 2 := by
  have hq : 0 < lg / (2 * (p + 1)) := by positivity
  have hev := (tendsto_log_affine_div C b hb).eventually (gt_mem_nhds hq)
  obtain ⟨a, ha⟩ := eventually_atTop.1 hev
  refine ⟨max a 1, le_trans zero_le_one (le_max_right _ _), fun t ht => ?_⟩
  have ht₁ : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have h₁ := ha t (le_trans (le_max_left _ _) ht)
  rw [div_lt_iff₀ ht₁] at h₁
  have h₂ : p * Real.log (C + b * t) ≤ p * (lg / (2 * (p + 1)) * t) :=
    mul_le_mul_of_nonneg_left h₁.le hp
  have h₃ : p * (lg / (2 * (p + 1)) * t) ≤ lg * t / 2 := by
    have hp₁ : 0 < p + 1 := by linarith
    rw [show p * (lg / (2 * (p + 1)) * t) = (lg * t / 2) * (p / (p + 1)) by field_simp]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hp₁).2 (by linarith))
  exact h₂.trans h₃
private lemma exists_relative_error (S lg Xi A G ρ p : ℝ) (hS : 0 < S) (hlg : 0 < lg) (hXi : 0 ≤ Xi) (hA : 0 ≤ A)
    (hG : 0 ≤ G) (hρ : 0 < ρ) (hp : 0 ≤ p) :
    ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧
      ∀ d x xK m lam : ℝ, 0 < d → d < 1 → 0 ≤ m → 0 < xK → xK ≤ Xi → 0 < x →
        |x - xK - S * lg * m| ≤ A + G * Real.log (1 + ρ * m) →
        m * lg = Real.log (1 / d) + lam → 0 ≤ lam → lam ≤ p * Real.log x →
        |x / (S * Real.log (1 / d)) - 1| ≤ e d := by
  set b : ℝ := S * lg + (G + 1) * ρ with hbdef
  set C : ℝ := 1 + Xi + A with hCdef
  have hb : 0 < b := by positivity
  have hC : 1 ≤ C := by rw [hCdef]; linarith
  obtain ⟨M₀, hM₀, hthr⟩ := exists_mul_log_affine_le_half C b lg p hb hlg hp
  set C' : ℝ := C + b * M₀ with hC'def
  set b' : ℝ := b * (2 / lg) with hb'def
  have hb' : 0 < b' := by positivity
  refine ⟨fun d => (A + Xi + (G + S * p) * Real.log (C' + b' * Real.log (1 / d))) / (S * Real.log (1 / d)), ?_, ?_⟩
  · have hℓ : Tendsto (fun d : ℝ => Real.log (1 / d)) (𝓝[>] 0) atTop := by
      simp only [one_div]
      exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have hE : Tendsto (fun l : ℝ => (A + Xi) / S * l⁻¹ + (G + S * p) / S * (Real.log (C' + b' * l) / l)) atTop
        (𝓝 ((A + Xi) / S * 0 + (G + S * p) / S * 0)) :=
      (tendsto_inv_atTop_zero.const_mul _).add ((tendsto_log_affine_div C' b' hb').const_mul _)
    simp only [mul_zero, add_zero] at hE
    refine (hE.comp hℓ).congr (fun d => ?_)
    simp only [Function.comp]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · intro d x xK m lam hd hd1 hm hxK hxKXi hx hline hsplit hlam hlamp
    have hℓ : 0 < Real.log (1 / d) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hd).2 hd1)
    set l : ℝ := Real.log (1 / d) with hldef
    have hlog₁ : Real.log (1 + ρ * m) ≤ ρ * m := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ρ * m by positivity)
      linarith
    have hlog₀ : 0 ≤ Real.log (1 + ρ * m) := Real.log_nonneg (by linarith [mul_nonneg hρ.le hm])
    have hVpos : ∀ t : ℝ, 0 ≤ t → 0 < C + b * t := fun t ht => by
      have := mul_nonneg hb.le ht
      linarith
    have hxV : x ≤ C + b * m := by
      have h₁ := (abs_le.1 hline).2
      have h₂ : G * Real.log (1 + ρ * m) ≤ G * (ρ * m) := mul_le_mul_of_nonneg_left hlog₁ hG
      have h₃ : 0 ≤ ρ * m := by positivity
      have h₄ : b * m = S * lg * m + G * (ρ * m) + ρ * m := by rw [hbdef]; ring
      rw [h₄, hCdef]
      linarith
    have h1V : 1 + ρ * m ≤ C + b * m := by
      have h₃ : 0 ≤ ρ * m := by positivity
      have h₄ : 0 ≤ S * lg * m := by positivity
      have h₅ : 0 ≤ G * (ρ * m) := by positivity
      have h₆ : b * m = S * lg * m + G * (ρ * m) + ρ * m := by rw [hbdef]; ring
      rw [h₆, hCdef]
      linarith
    have hlogx : Real.log x ≤ Real.log (C + b * m) := Real.log_le_log hx hxV
    have hmT : m ≤ M₀ + l * (2 / lg) := by
      by_cases hmM : m < M₀
      · have : 0 ≤ l * (2 / lg) := by positivity
        linarith
      · have h₁ := hthr m (not_lt.1 hmM)
        have h₂ : p * Real.log x ≤ p * Real.log (C + b * m) := mul_le_mul_of_nonneg_left hlogx hp
        have h₃ : m * lg ≤ 2 * l := by linarith
        have h₄ : m ≤ l * (2 / lg) := by
          rw [show l * (2 / lg) = 2 * l / lg by ring, le_div_iff₀ hlg]
          exact h₃
        linarith
    have hT : C + b * m ≤ C' + b' * l := by
      have h₁ := mul_le_mul_of_nonneg_left hmT hb.le
      have h₂ : b * (M₀ + l * (2 / lg)) = b * M₀ + b' * l := by rw [hb'def]; ring
      rw [hC'def]
      linarith
    have hlogT : Real.log (C + b * m) ≤ Real.log (C' + b' * l) := Real.log_le_log (hVpos m hm) hT
    set W : ℝ := Real.log (C' + b' * l) with hWdef
    have hlog1W : Real.log (1 + ρ * m) ≤ W :=
      (Real.log_le_log (by positivity) h1V).trans hlogT
    have hxW : Real.log x ≤ W := hlogx.trans hlogT
    have hdiff : |x - S * l| ≤ A + Xi + (G + S * p) * W := by
      have hid : x - S * l = (x - xK - S * lg * m) + xK + S * lam := by
        have : S * lg * m = S * l + S * lam := by
          rw [show S * lg * m = S * (m * lg) by ring, hsplit]
          ring
        rw [this]
        ring
      have h₁ : |x - S * l| ≤ |x - xK - S * lg * m| + |xK| + |S * lam| := by
        rw [hid]
        exact abs_add_three _ _ _
      have h₂ : |xK| ≤ Xi := by rw [abs_of_pos hxK]; exact hxKXi
      have h₃ : |S * lam| ≤ S * p * W := by
        rw [abs_of_nonneg (by positivity)]
        have : lam ≤ p * W := hlamp.trans (mul_le_mul_of_nonneg_left hxW hp)
        calc S * lam ≤ S * (p * W) := mul_le_mul_of_nonneg_left this hS.le
          _ = S * p * W := by ring
      have h₄ : G * Real.log (1 + ρ * m) ≤ G * W := mul_le_mul_of_nonneg_left hlog1W hG
      have h₅ : (G + S * p) * W = G * W + S * p * W := by ring
      rw [h₅]
      linarith
    have hSl : 0 < S * l := by positivity
    have heq : x / (S * l) - 1 = (x - S * l) / (S * l) := by
      rw [sub_div, div_self hSl.ne']
    show |x / (S * l) - 1| ≤ (A + Xi + (G + S * p) * W) / (S * l)
    rw [heq, abs_div, abs_of_pos hSl]
    exact div_le_div_of_nonneg_right hdiff hSl.le
theorem couplingAtDistanceStatement_holds (hline : couplingAlongLineStatement)
    (hpass : firstPassageExistsStatement) : couplingAtDistanceStatement := by
  intro T y D hD g hg hy p hp
  have hline' := hline T y D hD g hg hy
  have hpass' := hpass T y D hD g hg hy
  have hb := hD.errorMargin
  have hS : 0 < logSlope := by
    unfold logSlope
    positivity
  have hslope : 10 < logSlope * Real.log T.side := hb.slope_gt
  have hc₀ : D.c₀ = logSlope * Real.log T.side := rfl
  have hlg : 0 < Real.log T.side := by
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) hS.le
    linarith
  have hL : (0 : ℝ) < T.side := by
    rcases Nat.eq_zero_or_pos T.side with h | h
    · rw [h] at hlg
      simp at hlg
    · exact_mod_cast h
  have hX₀ : 0 < D.X₀ := by linarith [hb.floor_ge]
  have hρ : 0 < 3 * D.c₀ / (4 * D.X₀) := by positivity
  obtain ⟨e, he, hbound⟩ := exists_relative_error logSlope (Real.log T.side) |D.threshold g| |2 * D.cH + D.Cr|
    |8 * D.Md / (3 * D.c₀)| (3 * D.c₀ / (4 * D.X₀)) p hS hlg (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hρ hp
  refine ⟨e, he, ?_⟩
  intro K β _ hβ k hk d hd1 hlow hhigh
  obtain ⟨K', hK'⟩ := hpass' β hβ.1
  have hKK' : K' = K := by
    rcases lt_trichotomy K' K with h | h | h
    · exact absurd hK'.isFirstPassageIndex.1 (not_le.2 (hβ.2.2 K' h))
    · exact h
    · exact absurd hβ.2.1 (not_le.2 (hK'.isFirstPassageIndex.2 K h))
  subst hKK'
  have hg2 : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
  have hx : 0 < D.coupling β k := hg2.trans (hK'.coupling_gt k hk)
  have hxK : 0 < D.coupling β K' := hg2.trans (hK'.coupling_gt K' le_rfl)
  have hxKtop : D.coupling β K' ≤ |D.threshold g| := le_trans hK'.isFirstPassageIndex.1 (le_abs_self _)
  have ha : (0 : ℝ) < (T.side : ℝ) ^ ((k : ℤ) - K') := zpow_pos hL _
  have hd : 0 < d := by
    have : 0 < d / (T.side : ℝ) ^ ((k : ℤ) - K') := lt_of_lt_of_le one_pos hlow
    exact (div_pos_iff_of_pos_right ha).1 this
  have hmcast : ((K' - k : ℕ) : ℝ) = (K' : ℝ) - k := by
    rw [Nat.cast_sub hk]
  have hm : (0 : ℝ) ≤ ((K' - k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl := hline' K' β hβ k hk
  have hlog₀ : 0 ≤ Real.log (1 + 3 * D.c₀ / (4 * D.X₀) * ((K' - k : ℕ) : ℝ)) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hρ.le hm])
  have hline₂ : |D.coupling β k - D.coupling β K' - logSlope * Real.log T.side * ((K' - k : ℕ) : ℝ)| ≤
      |2 * D.cH + D.Cr| + |8 * D.Md / (3 * D.c₀)| *
        Real.log (1 + 3 * D.c₀ / (4 * D.X₀) * ((K' - k : ℕ) : ℝ)) := by
    rw [← hc₀, hmcast]
    refine hl.trans ?_
    unfold TrajectoryParameters.lineGap
    rw [hmcast, show 3 * D.c₀ * ((K' : ℝ) - k) / (4 * D.X₀) = 3 * D.c₀ / (4 * D.X₀) * ((K' : ℝ) - k) by ring]
    rw [hmcast] at hlog₀
    have h₁ := le_abs_self (2 * D.cH + D.Cr)
    have h₂ := mul_le_mul_of_nonneg_right (le_abs_self (8 * D.Md / (3 * D.c₀))) hlog₀
    linarith
  have hsplit : ((K' - k : ℕ) : ℝ) * Real.log T.side =
      Real.log (1 / d) + Real.log (d / (T.side : ℝ) ^ ((k : ℤ) - K')) := by
    rw [Real.log_div hd.ne' ha.ne', Real.log_zpow, one_div, Real.log_inv, hmcast]
    push_cast
    ring
  have hlam : 0 ≤ Real.log (d / (T.side : ℝ) ^ ((k : ℤ) - K')) := Real.log_nonneg hlow
  have hlamp : Real.log (d / (T.side : ℝ) ^ ((k : ℤ) - K')) ≤ p * Real.log (D.coupling β k) := by
    rw [← Real.log_rpow hx]
    exact Real.log_le_log (lt_of_lt_of_le one_pos hlow) hhigh
  exact hbound d (D.coupling β k) (D.coupling β K') _ _ hd hd1 hm hxK hxKtop hx hline₂ hsplit hlam hlamp
end YangMills.Construction.TrajectoryData
end
