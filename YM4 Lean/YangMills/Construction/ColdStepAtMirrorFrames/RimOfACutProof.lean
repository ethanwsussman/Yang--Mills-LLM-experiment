import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open Set
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
namespace CutoffFactor
theorem eq_of_hasDerivAt_zero_on_Ioo {g : ℝ → ℝ} {a b : ℝ} (hg : ∀ x ∈ Ioo a b, HasDerivAt g 0 x) {x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : g x = g y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  rcases hxy.lt_or_eq with h | h
  · have hsub : Icc x y ⊆ Ioo a b := fun t ht => ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    obtain ⟨t, ht, hs⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0 : ℝ)) h
      (fun t ht => (hg t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => hg t (hsub (Ioo_subset_Icc_self ht)))
    have hne : y - x ≠ 0 := by linarith
    have := (eq_div_iff hne).mp hs
    linarith
  · rw [h]
theorem hasDerivAt_zero_of_abs_le_sq {f : ℝ → ℝ} {a C : ℝ} (hC : 0 ≤ C) (ha : f a = 0)
    (h : ∀ᶠ x in nhds a, |f x| ≤ C * (x - a) ^ 2) : HasDerivAt f 0 a := by
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hb : Metric.ball a (c / (C + 1)) ∈ nhds a := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [h, hb] with x hx hxb
  have h1 : |x - a| < c / (C + 1) := by simpa [Real.dist_eq] using hxb
  simp only [ha, sub_zero, smul_zero, Real.norm_eq_abs]
  rw [lt_div_iff₀ (by positivity)] at h1
  have h2 : C * (x - a) ^ 2 = C * |x - a| * |x - a| := by
    rw [mul_assoc, abs_mul_abs_self]
    ring
  have h3 := abs_nonneg (x - a)
  rw [h2] at hx
  nlinarith
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem cutoff_contDiffAt (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p u :=
  hp.smooth.contDiffAt (Ico_mem_nhds h0 h1)
theorem cutoff_hasDerivAt (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt p (deriv p u) u :=
  ((cutoff_contDiffAt hp h0 h1).differentiableAt (by simp)).hasDerivAt
theorem cutoff_deriv_contDiffOn (hp : IsCutoff ρ p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv p) (Ioo 0 ρ) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp
    (hp.smooth.mono Ioo_subset_Ico_self)).2
theorem cutoff_hasDerivAt_deriv (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt (deriv p) (deriv (deriv p) u) u :=
  (((cutoff_deriv_contDiffOn hp).contDiffAt (Ioo_mem_nhds h0 h1)).differentiableAt (by simp)).hasDerivAt
theorem eq_inv_sq_add_affine_near_edge (hρ : 0 < ρ) (hp : IsCutoff ρ p) : ∃ c A B : ℝ, 0 < c ∧ c < ρ ∧
    ∀ u ∈ Ioo c ρ, deriv p u = ((ρ - u) ^ 3)⁻¹ / 3 + A ∧
      p u = ((ρ - u) ^ 2)⁻¹ / 6 + A * u + B := by
  obtain ⟨u₀, hu₀, hrim⟩ := hp.rim_second_deriv
  set c := max u₀ (ρ / 2) with hc
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hcρ : c < ρ := max_lt hu₀ (by linarith)
  set um := (c + ρ) / 2 with hum
  have humI : um ∈ Ioo c ρ := ⟨by simp only [hum]; linarith, by simp only [hum]; linarith⟩
  have hi : ∀ u ∈ Ioo c ρ, 0 < ρ - u := fun u hu => by linarith [hu.2]
  have hd3 : ∀ u ∈ Ioo c ρ, HasDerivAt (fun v => ((ρ - v) ^ 3)⁻¹ / 3) (((ρ - u) ^ 4)⁻¹) u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => (ρ - v) ^ 3) (3 * (ρ - u) ^ 2 * (-1)) u := by
      have := ((hasDerivAt_id u).const_sub ρ).fun_pow 3
      exact HasDerivAt.congr_deriv this (by simp)
    have hne : (ρ - u) ^ 3 ≠ 0 := (pow_pos (hi u hu) 3).ne'
    refine HasDerivAt.congr_deriv ((h1.fun_inv hne).div_const 3) ?_
    have := hi u hu
    field_simp
    try ring
  have hd2 : ∀ u ∈ Ioo c ρ, HasDerivAt (fun v => ((ρ - v) ^ 2)⁻¹ / 6) (((ρ - u) ^ 3)⁻¹ / 3) u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => (ρ - v) ^ 2) (2 * (ρ - u) * (-1)) u := by
      have := ((hasDerivAt_id u).const_sub ρ).fun_pow 2
      exact HasDerivAt.congr_deriv this (by simp)
    have hne : (ρ - u) ^ 2 ≠ 0 := (pow_pos (hi u hu) 2).ne'
    refine HasDerivAt.congr_deriv ((h1.fun_inv hne).div_const 6) ?_
    have := hi u hu
    field_simp
    try ring
  set A := deriv p um - ((ρ - um) ^ 3)⁻¹ / 3 with hA
  have hfirst : ∀ u ∈ Ioo c ρ, deriv p u = ((ρ - u) ^ 3)⁻¹ / 3 + A := by
    intro u hu
    have hz : ∀ v ∈ Ioo c ρ, HasDerivAt (fun w => deriv p w - ((ρ - w) ^ 3)⁻¹ / 3) 0 v := by
      intro v hv
      have h1 := cutoff_hasDerivAt_deriv hp (hc0.trans hv.1) hv.2
      have e : deriv (deriv p) v = ((ρ - v) ^ 4)⁻¹ :=
        hrim v (lt_of_le_of_lt (le_max_left _ _) hv.1) hv.2
      rw [e] at h1
      exact HasDerivAt.congr_deriv (h1.sub (hd3 v hv)) (by ring)
    have := eq_of_hasDerivAt_zero_on_Ioo hz hu humI
    simp only [hA]
    linarith
  set B := p um - ((ρ - um) ^ 2)⁻¹ / 6 - A * um with hB
  refine ⟨c, A, B, hc0, hcρ, fun u hu => ⟨hfirst u hu, ?_⟩⟩
  have hz : ∀ v ∈ Ioo c ρ, HasDerivAt (fun w => p w - ((ρ - w) ^ 2)⁻¹ / 6 - A * w) 0 v := by
    intro v hv
    have h1 := cutoff_hasDerivAt hp (hc0.trans hv.1) hv.2
    rw [hfirst v hv] at h1
    have h2 : HasDerivAt (fun w : ℝ => A * w) A v := by
      simpa using (hasDerivAt_id v).const_mul A
    exact HasDerivAt.congr_deriv ((h1.sub (hd2 v hv)).sub h2) (by ring)
  have := eq_of_hasDerivAt_zero_on_Ioo hz hu humI
  simp only [hB]
  linarith
theorem exp_neg_le_pow_near_edge (hρ : 0 < ρ) (hp : IsCutoff ρ p) : ∃ c C : ℝ, 0 < c ∧ c < ρ ∧ 0 ≤ C ∧
    ∀ u ∈ Ioo c ρ, Real.exp (- p u) ≤ C * (ρ - u) ^ 6 ∧
      |deriv p u| * Real.exp (- p u) ≤ C * (ρ - u) ^ 3 := by
  obtain ⟨c, A, B, hc0, hcρ, hform⟩ := eq_inv_sq_add_affine_near_edge hρ hp
  set K := Real.exp (|A| * ρ + |B|) with hK
  have hK0 : 0 < K := Real.exp_pos _
  refine ⟨c, 1296 * K * (1 + |A| * ρ ^ 3), hc0, hcρ, by positivity, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hform u hu
  set w := ρ - u with hw
  have hw0 : 0 < w := by
    have := hu.2
    simp only [hw]
    linarith
  have hwρ : w ≤ ρ := by
    have := hc0.trans hu.1
    simp only [hw]
    linarith
  set y := (w ^ 2)⁻¹ / 6 with hy
  have hy0 : 0 < y := by positivity
  have he : Real.exp (- y) ≤ 1296 * w ^ 6 := by
    have h3 := Real.pow_div_factorial_le_exp y hy0.le 3
    have h4 : Real.exp (- y) * Real.exp y = 1 := by
      rw [← Real.exp_add]
      simp
    have h5 : y ^ 3 * (1296 * w ^ 6) = 6 := by
      simp only [hy]
      field_simp
      norm_num
    have hE := Real.exp_pos (- y)
    have h6 : y ^ 3 / (Nat.factorial 3 : ℝ) = y ^ 3 / 6 := by norm_num [Nat.factorial]
    rw [h6] at h3
    have hy3 : 0 < y ^ 3 := by positivity
    have h7 : Real.exp (- y) * (y ^ 3 / 6) ≤ 1 := by
      rw [← h4]
      exact mul_le_mul_of_nonneg_left h3 hE.le
    have h8 : Real.exp (- y) * y ^ 3 ≤ 1296 * w ^ 6 * y ^ 3 := by
      nlinarith
    exact le_of_mul_le_mul_right h8 hy3
  have hlin : -(A * u + B) ≤ |A| * ρ + |B| := by
    have hur : u ≤ ρ := hu.2.le
    have e1 := neg_abs_le A
    have e2 := neg_abs_le B
    have e3 : |A| * u ≤ |A| * ρ := mul_le_mul_of_nonneg_left hur (abs_nonneg _)
    nlinarith
  have hexp : Real.exp (- p u) ≤ 1296 * K * w ^ 6 := by
    have e : - p u = - y + -(A * u + B) := by
      rw [h2]
      ring
    rw [e, Real.exp_add]
    have h3 : Real.exp (-(A * u + B)) ≤ K := Real.exp_le_exp.mpr hlin
    calc Real.exp (- y) * Real.exp (-(A * u + B)) ≤ (1296 * w ^ 6) * K :=
          mul_le_mul he h3 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hge : (1 : ℝ) ≤ 1 + |A| * ρ ^ 3 := by
    have : 0 ≤ |A| * ρ ^ 3 := by positivity
    linarith
  constructor
  · calc Real.exp (- p u) ≤ 1296 * K * w ^ 6 := hexp
      _ ≤ 1296 * K * (1 + |A| * ρ ^ 3) * w ^ 6 := by
        have : 0 ≤ 1296 * K * w ^ 6 := by positivity
        nlinarith
  · have habs : |deriv p u| ≤ (w ^ 3)⁻¹ / 3 + |A| := by
      rw [h1]
      calc |(w ^ 3)⁻¹ / 3 + A| ≤ |(w ^ 3)⁻¹ / 3| + |A| := abs_add_le _ _
        _ = (w ^ 3)⁻¹ / 3 + |A| := by rw [abs_of_pos (by positivity)]
    have hw3 : w ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hw0.le hwρ 3
    calc |deriv p u| * Real.exp (- p u) ≤ ((w ^ 3)⁻¹ / 3 + |A|) * (1296 * K * w ^ 6) :=
          mul_le_mul habs hexp (Real.exp_pos _).le (by positivity)
      _ = 1296 * K * (w ^ 3 / 3 + |A| * w ^ 3 * w ^ 3) := by
          field_simp
      _ ≤ 1296 * K * (1 + |A| * ρ ^ 3) * w ^ 3 := by
          have h3 : |A| * w ^ 3 * w ^ 3 ≤ |A| * ρ ^ 3 * w ^ 3 := by
            have : 0 ≤ |A| * w ^ 3 := by positivity
            have h4 : 0 < w ^ 3 := by positivity
            nlinarith [abs_nonneg A]
          have h5 : 0 < w ^ 3 := by positivity
          have h6 : 0 < 1296 * K := by positivity
          nlinarith
end CutoffFactor
open CutoffFactor in
theorem cutoffFactor_isRadialCutoff : CutoffFactorIsRadialCutoff := by
  intro ρ p hρ hp
  obtain ⟨c, C, hc0, hcρ, hC0, hb⟩ := exp_neg_le_pow_near_edge hρ hp
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hr
  set D : ℝ → ℝ := fun u => if 0 < u ∧ u < ρ then - deriv p u * Real.exp (- p u) else 0 with hD
  have hone : ∀ u, u ≤ 5 * ρ / 8 → r u = 1 := by
    intro u hu
    have h1 : max u 0 ≤ 5 * ρ / 8 := max_le hu (by positivity)
    simp only [hr, cutoffFactor]
    rw [if_pos (by linarith), hp.vanish_small _ (le_max_right _ _) h1]
    simp
  have hzero : ∀ u, ρ ≤ u → r u = 0 := by
    intro u hu
    simp only [hr, cutoffFactor]
    rw [if_neg]
    exact not_lt.mpr (hu.trans (le_max_left _ _))
  have hin : ∀ u, 0 < u → u < ρ → r u = Real.exp (- p u) := by
    intro u h0 h1
    simp only [hr, cutoffFactor]
    rw [max_eq_left h0.le, if_pos h1]
  have hdz : ∀ u, 0 < u → u < 5 * ρ / 8 → deriv p u = 0 := by
    intro u h0 h1
    have e : p =ᶠ[nhds u] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds h0 h1] with v hv
      exact hp.vanish_small v hv.1.le hv.2.le
    rw [e.deriv_eq]
    simp
  have hDz : ∀ u, u < 5 * ρ / 8 → D u = 0 := by
    intro u h1
    simp only [hD]
    by_cases h0 : 0 < u
    · rw [hdz u h0 h1]
      simp
    · rw [if_neg fun h => h0 h.1]
  have hDρ : ∀ u, ρ ≤ u → D u = 0 := by
    intro u h1
    simp only [hD]
    rw [if_neg fun h => absurd h.2 (not_lt.mpr h1)]
  have hρ' : 5 * ρ / 8 < ρ := by linarith
  have hasD : ∀ u, HasDerivAt r (D u) u := by
    intro u
    rcases lt_or_ge u (5 * ρ / 8) with h1 | h1
    · rw [hDz u h1]
      have e : r =ᶠ[nhds u] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds h1] with v hv
        exact hone v (le_of_lt hv)
      exact (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq e
    · rcases lt_trichotomy u ρ with h2 | h2 | h2
      · have h0 : 0 < u := by
          have : 0 < 5 * ρ / 8 := by positivity
          linarith
        have e : r =ᶠ[nhds u] fun v => Real.exp (- p v) := by
          filter_upwards [Ioo_mem_nhds h0 h2] with v hv
          exact hin v hv.1 hv.2
        have h3 := ((cutoff_hasDerivAt hp h0 h2).fun_neg.exp).congr_of_eventuallyEq e
        refine HasDerivAt.congr_deriv h3 ?_
        simp only [hD]
        rw [if_pos ⟨h0, h2⟩]
        ring
      · subst h2
        rw [hDρ u le_rfl]
        apply hasDerivAt_zero_of_abs_le_sq (C := C * u ^ 4) (by positivity) (hzero u le_rfl)
        filter_upwards [Ioi_mem_nhds hcρ] with x hx
        rcases lt_or_ge x u with h3 | h3
        · have h4 := (hb x ⟨hx, h3⟩).1
          rw [hin x (hc0.trans hx) h3, abs_of_pos (Real.exp_pos _)]
          have hv0 : 0 < u - x := by linarith
          have hv1 : u - x ≤ u := by
            have := hc0.trans hx
            linarith
          have h5 : (u - x) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ hv0.le hv1 4
          calc Real.exp (- p x) ≤ C * (u - x) ^ 6 := h4
            _ = C * (u - x) ^ 4 * (x - u) ^ 2 := by ring
            _ ≤ C * u ^ 4 * (x - u) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact mul_le_mul_of_nonneg_left h5 hC0
        · rw [hzero x h3, abs_zero]
          positivity
      · rw [hDρ u h2.le]
        have e : r =ᶠ[nhds u] fun _ => (0 : ℝ) := by
          filter_upwards [Ioi_mem_nhds h2] with v hv
          exact hzero v (le_of_lt hv)
        exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq e
  have hcontD : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro u
    rcases lt_or_ge u (5 * ρ / 8) with h1 | h1
    · have e : D =ᶠ[nhds u] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h1] with v hv
        exact hDz v hv
      exact continuousAt_const.congr e.symm
    · rcases lt_trichotomy u ρ with h2 | h2 | h2
      · have h0 : 0 < u := by
          have : 0 < 5 * ρ / 8 := by positivity
          linarith
        have e : D =ᶠ[nhds u] fun v => - deriv p v * Real.exp (- p v) := by
          filter_upwards [Ioo_mem_nhds h0 h2] with v hv
          simp only [hD]
          rw [if_pos ⟨hv.1, hv.2⟩]
        have c1 : ContinuousAt (deriv p) u :=
          ((cutoff_deriv_contDiffOn hp).continuousOn).continuousAt (Ioo_mem_nhds h0 h2)
        have c2 : ContinuousAt p u := (cutoff_hasDerivAt hp h0 h2).continuousAt
        exact (c1.neg.mul (c2.neg.rexp)).congr e.symm
      · subst h2
        have h3 : Filter.Tendsto D (nhds u) (nhds 0) := by
          have hlim : Filter.Tendsto (fun x : ℝ => C * |x - u| ^ 3) (nhds u) (nhds 0) := by
            have hc : Continuous fun x : ℝ => C * |x - u| ^ 3 := by fun_prop
            have := hc.tendsto u
            simpa using this
          apply squeeze_zero_norm' _ hlim
          filter_upwards [Ioi_mem_nhds hcρ] with x hx
          rcases lt_or_ge x u with h4 | h4
          · have h5 := (hb x ⟨hx, h4⟩).2
            simp only [hD]
            rw [if_pos ⟨hc0.trans hx, h4⟩, Real.norm_eq_abs, abs_mul, abs_neg,
              abs_of_pos (Real.exp_pos _), abs_sub_comm x u, abs_of_pos (by linarith : 0 < u - x)]
            exact h5
          · rw [hDρ x h4, norm_zero]
            positivity
        have h4 : D u = 0 := hDρ u le_rfl
        rw [ContinuousAt, h4]
        exact h3
      · have e : D =ᶠ[nhds u] fun _ => (0 : ℝ) := by
          filter_upwards [Ioi_mem_nhds h2] with v hv
          exact hDρ v (le_of_lt hv)
        exact continuousAt_const.congr e.symm
  have hderiv : deriv r = D := funext fun u => (hasD u).deriv
  refine ⟨?_, hzero, ?_, ?_, ?_⟩
  · intro u h0 h1
    simp only [hr, cutoffFactor]
    rw [max_eq_left h0, if_pos h1]
    exact Real.exp_pos _
  · intro u h0 h1
    exact hone u h1
  · rw [contDiff_one_iff_deriv]
    exact ⟨fun u => (hasD u).differentiableAt, by rw [hderiv]; exact hcontD⟩
  · intro u h0
    rw [hderiv]
    simp only [hD]
    split_ifs with hcase
    · have hmono : MonotoneOn (deriv p) (Ioo 0 ρ) :=
        (hp.convex.subset Ioo_subset_Ico_self (convex_Ioo 0 ρ)).monotoneOn_deriv
          fun x hx => (cutoff_hasDerivAt hp hx.1 hx.2).differentiableAt
      have hnn : 0 ≤ deriv p u := by
        have hq : (ρ / 4) ∈ Ioo 0 ρ := ⟨by positivity, by linarith⟩
        have hq0 : deriv p (ρ / 4) = 0 := hdz _ hq.1 (by linarith)
        rcases le_total (ρ / 4) u with h | h
        · have := hmono hq ⟨hcase.1, hcase.2⟩ h
          rwa [hq0] at this
        · rw [hdz u hcase.1 (by linarith)]
      have := Real.exp_pos (- p u)
      nlinarith
    · exact le_rfl
end ColdStepAtMirrorFrames
end YangMills.Construction
end
