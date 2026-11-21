import YangMills.Construction.FourPointCondition.LevelForEveryScaleProof
import YangMills.Construction.ParameterData.FirstPassageOfTheFlow
import YangMills.Construction.ParameterData.TheCouplingAlongTheLine
import YangMills.Construction.SystemOfAdmissibleConstants.EnvelopesOfTheLevel
import YangMills.Construction.SystemOfAdmissibleConstants.LevelOfADistance
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open RenormalizationStepParameters TrajectoryData StateLaws TorusLumps AdmissibleConstants
private lemma logSlope_pos : 0 < logSlope := by
  unfold logSlope
  have := Real.pi_pos
  positivity
private lemma logSlope_le_half : logSlope ≤ 1 / 2 := by
  unfold logSlope
  have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h0 : 0 < 3 * Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ h0]
  nlinarith
private lemma one_le_clusterRange {x : ℝ} (hx : 0 < x) : (1 : ℝ) ≤ clusterRange x := by apply _root_.YangMills.SharedProofs.p30320 <;> assumption
private lemma clusterRange_mono {x x' : ℝ} (h0 : 0 ≤ x) (h : x ≤ x') :
    (clusterRange x : ℝ) ≤ clusterRange x' := by
  have h1 : x ^ ((1 : ℝ) / 100) ≤ x' ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow h0 h (by norm_num)
  exact_mod_cast Nat.ceil_mono h1
private lemma log_clusterRange_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (clusterRange x) ≤ 1 + Real.log x / 100 := by
  have hx0 : 0 < x := by linarith
  have hp : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx (by norm_num)
  have hr : (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
    have h1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x ^ ((1 : ℝ) / 100))).le
    have h2 : (clusterRange x : ℝ) ≤ x ^ ((1 : ℝ) / 100) + 1 := h1
    linarith
  have h3 := Real.log_le_log (lt_of_lt_of_le one_pos (one_le_clusterRange hx0)) hr
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h3
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  linarith
private lemma height_le_log_bound (P Q Λ lL w G b : ℝ) (hP : 1 ≤ P) (hQ : 0 ≤ Q) (hΛ : 0 ≤ Λ)
    (hl : 0 < lL) (hw : 0 ≤ w) (hG : 0 ≤ G) (hb : 0 ≤ b) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ u ρ : ℝ, 0 < u → 0 ≤ ρ → ρ ≤ 1 + Real.log (P + Q * u) →
      G * Real.log (1 + w * ((Λ + ρ + u) / lL)) + b * (Λ + ρ) ≤ C₁ + C₂ * Real.log (1 + u) := by
  set A₁ : ℝ := Real.log (P + Q) with hA₁
  have hA₁0 : 0 ≤ A₁ := Real.log_nonneg (by linarith)
  set A₂ : ℝ := (Λ + 1 + A₁ + 2) / lL with hA₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨G * Real.log (1 + w * A₂) + b * (Λ + 1 + A₁), G + b, ?_, by positivity, ?_⟩
  · have : 0 ≤ Real.log (1 + w * A₂) := Real.log_nonneg (by nlinarith [mul_nonneg hw hA₂0])
    positivity
  intro u ρ hu hρ0 hρ
  set v : ℝ := Real.log (1 + u) with hv
  have hv0 : 0 ≤ v := Real.log_nonneg (by linarith)
  have hvu : v ≤ u := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)
    linarith
  have hPQ : Real.log (P + Q * u) ≤ A₁ + v := by
    rw [hA₁, hv, ← Real.log_mul (by linarith) (by linarith)]
    refine Real.log_le_log (by nlinarith [mul_nonneg hQ hu.le]) ?_
    nlinarith [mul_nonneg hQ hu.le, mul_nonneg (by linarith : 0 ≤ P) hu.le]
  have hρ' : ρ ≤ 1 + A₁ + v := by linarith
  have hm0 : 0 ≤ (Λ + ρ + u) / lL := by positivity
  have hm : (Λ + ρ + u) / lL ≤ A₂ * (1 + u) := by
    rw [hA₂, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hl.le
    nlinarith [mul_nonneg hΛ hu.le, mul_nonneg hA₁0 hu.le]
  have harg : 1 + w * ((Λ + ρ + u) / lL) ≤ (1 + w * A₂) * (1 + u) := by
    have h1 : w * ((Λ + ρ + u) / lL) ≤ w * (A₂ * (1 + u)) := mul_le_mul_of_nonneg_left hm hw
    nlinarith
  have hlog : Real.log (1 + w * ((Λ + ρ + u) / lL)) ≤ Real.log (1 + w * A₂) + v := by
    rw [hv, ← Real.log_mul (by nlinarith [mul_nonneg hw hA₂0]) (by linarith)]
    exact Real.log_le_log (by nlinarith [mul_nonneg hw hm0]) harg
  have h1 := mul_le_mul_of_nonneg_left hlog hG
  have h2 : b * (Λ + ρ) ≤ b * (Λ + (1 + A₁ + v)) :=
    mul_le_mul_of_nonneg_left (by linarith) hb
  nlinarith
private lemma ratio_bounded_and_tendsto_zero (Hf xf : ℝ → ℝ) (a A C₀ C₁ C₂ : ℝ) (ha : 0 < a)
    (hA : 0 < A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hx : ∀ d, 0 < d → d < 1 → xf d = A + a * Real.log (1 / d))
    (hlo : ∀ d, 0 < d → d < 1 → C₀ ≤ Hf d)
    (hhi : ∀ d, 0 < d → d < 1 → Hf d ≤ C₁ + C₂ * Real.log (1 + Real.log (1 / d))) :
    BddAbove ((fun d => Hf d / xf d) '' Set.Ioo 0 1) ∧
      Tendsto (fun d => Hf d / xf d) (𝓝[>] 0) (𝓝 0) := by
  have hu : ∀ d : ℝ, 0 < d → d < 1 → 0 < Real.log (1 / d) := fun d h0 h1 =>
    Real.log_pos (by rw [lt_div_iff₀ h0]; linarith)
  have hxpos : ∀ d : ℝ, 0 < d → d < 1 → 0 < xf d := fun d h0 h1 => by
    rw [hx d h0 h1]
    have := mul_pos ha (hu d h0 h1)
    linarith
  constructor
  · refine ⟨C₁ / A + C₂ / a, ?_⟩
    rintro _ ⟨d, ⟨h0, h1⟩, rfl⟩
    have hup := hu d h0 h1
    have hxp := hxpos d h0 h1
    show Hf d / xf d ≤ _
    rw [div_le_iff₀ hxp]
    have hvu : Real.log (1 + Real.log (1 / d)) ≤ Real.log (1 / d) := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log (1 / d) by linarith)
      linarith
    have e1 : C₁ ≤ C₁ / A * xf d := by
      rw [hx d h0 h1, div_mul_eq_mul_div, le_div_iff₀ hA]
      have := mul_nonneg hC₁ (mul_pos ha hup).le
      nlinarith
    have e2 : C₂ * Real.log (1 / d) ≤ C₂ / a * xf d := by
      rw [hx d h0 h1, div_mul_eq_mul_div, le_div_iff₀ ha]
      have := mul_nonneg hC₂ hA.le
      nlinarith
    have e3 := mul_le_mul_of_nonneg_left hvu hC₂
    have e4 := hhi d h0 h1
    nlinarith
  · have ht : Tendsto (fun d : ℝ => 1 + Real.log (1 / d)) (𝓝[>] 0) atTop := by
      have h1 : Tendsto (fun d : ℝ => Real.log (1 / d)) (𝓝[>] 0) atTop := by
        simp only [one_div]
        exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
      exact tendsto_atTop_add_const_left _ _ h1
    have hl0 := (Real.tendsto_pow_log_div_mul_add_atTop a (A - a) 0 ha.ne').comp ht
    have hl1 := (Real.tendsto_pow_log_div_mul_add_atTop a (A - a) 1 ha.ne').comp ht
    have hlow := hl0.const_mul C₀
    have hup := (hl0.const_mul C₁).add (hl1.const_mul C₂)
    simp only [mul_zero, add_zero] at hlow hup
    have hev : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < 1 := by
      have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [this] with d hd using hd
    have hden : ∀ d : ℝ, 0 < d → d < 1 → a * (1 + Real.log (1 / d)) + (A - a) = xf d :=
      fun d h0 h1 => by
        rw [hx d h0 h1]
        ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hev] with d hd
      simp only [Function.comp, pow_zero, hden d hd.1 hd.2]
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (hlo d hd.1 hd.2) (hxpos d hd.1 hd.2).le
    · filter_upwards [hev] with d hd
      simp only [Function.comp, pow_zero, pow_one, hden d hd.1 hd.2]
      rw [mul_one_div, mul_div_assoc', ← add_div]
      exact div_le_div_of_nonneg_right (hhi d hd.1 hd.2) (hxpos d hd.1 hd.2).le
private lemma admissible_basics {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    (hD : D.Admissible) :
    (2 : ℝ) ≤ T.side ∧ 0 ≤ D.cH ∧ 8 ≤ D.X₀ ∧ 0 ≤ D.Md ∧ 0 ≤ D.Cr ∧ 0 ≤ D.shift ∧ 10 < D.c₀ := by
  have hfits := hD.errorMargin.admissible
  have hL : (2 ^ 16 : ℕ) ≤ T.side := hfits.L_ge
  have hB : 0 < T.B := hfits.B_pos
  refine ⟨?_, ?_, hD.errorMargin.floor_ge, ?_, hD.errorMargin.Cr_nonneg, ?_, hD.errorMargin.slope_gt⟩
  · have h1 : 2 ≤ T.side := le_trans (by norm_num) hL
    exact_mod_cast h1
  · have h1 := hD.errorMargin.slope 0 0 le_rfl
    simp at h1
    linarith
  · exact le_trans (abs_nonneg _) (hD.errorMargin.secondStep_le 0)
  · have := hD.shift_ge
    linarith
private lemma inverseCouplingFloor_facts {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    {G : ℝ} (hfl : inverseCouplingFloor D ≤ G) :
    D.floorStar ≤ G ∧ D.X₀ ≤ G ∧ 2 * D.cH + 9 ≤ G := by
  have h1 : D.floorStar ≤ inverseCouplingFloor D := le_max_left _ _
  have h2 : D.X₀ ≤ D.floorStar := le_trans (le_max_left _ _) (le_max_left _ _)
  have h3 : 2 * D.cH + 9 ≤ inverseCouplingFloor D :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  exact ⟨by linarith, by linarith, by linarith⟩
private lemma inv_sq_eq_zpow (g : ℝ) : (g ^ 2)⁻¹ = g ^ (-2 : ℤ) := by
  rw [zpow_neg]
  norm_cast
private lemma envelopes_at_level {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    (hD : D.Admissible) {g : ℝ} (hg0 : 0 < g) (hfl : inverseCouplingFloor D ≤ g ^ (-2 : ℤ))
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) {K : ℕ} {β : ℝ} (hw : β ∈ D.passageWindow K g)
    {k : ℕ} (hk : k < K)
    (hfar : 2 ^ 12 * (clusterRange (D.coupling β k) : ℝ) ≤ d * (T.side : ℝ) ^ (K - k))
    (hnear : d * (T.side : ℝ) ^ (K - k) ≤ 2 ^ 13 * (T.side : ℝ) * (clusterRange (D.coupling β k) : ℝ))
    (hline : |D.coupling β k - D.coupling β K - D.c₀ * ((K : ℝ) - k)| ≤ D.lineGap (K - k))
    (hK : g ^ (-2 : ℤ) < D.coupling β K) :
    lowerCouplingEnvelope D g d ≤ D.coupling β k ∧ D.coupling β k ≤ upperCouplingEnvelope D g d ∧
      (K : ℝ) - k ≤ scaleDepthEnvelope D g d ∧
      |logSlope * Real.log (1 / d) - D.coupling β k| ≤ heightBound D g d := by
  obtain ⟨hL, hc, hX, hMd, hCr, hBs, hc0⟩ := admissible_basics D hD
  obtain ⟨-, hGX, hG9⟩ := inverseCouplingFloor_facts D hfl
  have hw' : SequencePassage.passageThreshold D.shift g ≤ β ∧
      SequencePassage.IsFirstPassageIndex D.shift g (D.coupling β) K := hw
  have hxKtop : D.coupling β K ≤ D.threshold g := hw'.2.1
  have habove : ∀ l < K, D.threshold g < D.coupling β l := hw'.2.2
  have htop : D.threshold g = g ^ (-2 : ℤ) + D.shift := rfl
  have hb := logSlope_pos
  have hbh := logSlope_le_half
  have hxk : D.threshold g < D.coupling β k := habove k hk
  have hlL : 0 < Real.log (T.side : ℝ) := Real.log_pos (by linarith)
  have hc0' : D.c₀ = logSlope * Real.log (T.side : ℝ) := rfl
  have hcast : ((K - k : ℕ) : ℝ) = (K : ℝ) - k := Nat.cast_sub hk.le
  have hline2 : 3 / 4 * D.c₀ * ((K : ℝ) - k) - 2 * D.cH ≤ D.coupling β k - D.coupling β K ∧
      D.coupling β k - D.coupling β K ≤ 5 / 4 * D.c₀ * ((K : ℝ) - k) + 2 * D.cH :=
    hD.errorMargin.drop_two_sided β k K hk.le fun l hl => by
      have h1 : D.threshold g < D.coupling β l := habove l hl
      show D.X₀ ≤ D.coupling β l
      linarith
  set x := D.coupling β k with hxdef
  set xK := D.coupling β K with hxKdef
  set m : ℝ := (K : ℝ) - k with hmdef
  set b := logSlope with hbdef
  set u : ℝ := Real.log (1 / d) with hudef
  have hu : u = - Real.log d := by
    rw [hudef, one_div, Real.log_inv]
  have hu0 : 0 < u := by
    rw [hu]
    have := Real.log_neg hd0 hd1
    linarith
  have hx1 : 1 ≤ x := by
    rw [htop] at hxk
    linarith
  have hx0 : 0 < x := by linarith
  set n : ℝ := d * (T.side : ℝ) ^ (K - k) with hndef
  have hn0 : 0 < n := by positivity
  have hn1 : 1 ≤ n := by
    have := one_le_clusterRange hx0
    linarith
  set ln : ℝ := Real.log n with hlndef
  have hln0 : 0 ≤ ln := Real.log_nonneg hn1
  have hlogn : ln = Real.log d + m * Real.log (T.side : ℝ) := by
    rw [hlndef, hndef, Real.log_mul hd0.ne' (by positivity), Real.log_pow, hcast]
  have key : D.c₀ * m = b * ln + b * u := by
    rw [hc0', hlogn, hu]
    ring
  set Λ : ℝ := Real.log (2 ^ 13 * (T.side : ℝ)) with hΛ
  have hrx : (0 : ℝ) < clusterRange x := lt_of_lt_of_le one_pos (one_le_clusterRange hx0)
  have hln_le : ln ≤ Λ + Real.log (clusterRange x) := by
    rw [hΛ, ← Real.log_mul (by positivity) hrx.ne']
    exact Real.log_le_log hn0 hnear
  have hlogr := log_clusterRange_le hx1
  have hlogx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hbl : b * ln ≤ b * Λ + 1 / 2 * (1 + x / 100) := by
    have h1 : ln ≤ Λ + (1 + x / 100) := by linarith
    have h2 : b * ln ≤ b * (Λ + (1 + x / 100)) := mul_le_mul_of_nonneg_left h1 hb.le
    have h3 : b * (1 + x / 100) ≤ 1 / 2 * (1 + x / 100) :=
      mul_le_mul_of_nonneg_right hbh (by positivity)
    linarith [mul_add b Λ (1 + x / 100)]
  have hbln0 : 0 ≤ b * ln := mul_nonneg hb.le hln0
  have hlower : lowerCouplingEnvelope D g d ≤ x := by
    have h1 := hline2.1
    have e1 : 3 / 4 * D.c₀ * m = 3 / 4 * (b * ln + b * u) := by rw [← key]; ring
    have e2 : lowerCouplingEnvelope D g d = g ^ (-2 : ℤ) - 2 * D.cH + 3 / 4 * (b * u) := by
      unfold lowerCouplingEnvelope
      rw [inv_sq_eq_zpow]
      ring
    rw [e2]
    linarith
  have hupper : x ≤ upperCouplingEnvelope D g d := by
    have h1 := hline2.2
    have e1 : 5 / 4 * D.c₀ * m = 5 / 4 * (b * ln + b * u) := by rw [← key]; ring
    have e2 : upperCouplingEnvelope D g d =
        2 * (D.threshold g + 2 * D.cH + 1 + (5 / 4 * (b * u) + 5 / 4 * (b * Λ))) := by
      unfold upperCouplingEnvelope
      ring
    rw [e2]
    linarith
  refine ⟨hlower, hupper, ?_⟩
  set xp := upperCouplingEnvelope D g d with hxp
  have hrp : (clusterRange x : ℝ) ≤ clusterRange xp := clusterRange_mono hx0.le hupper
  have hrp0 : (0 : ℝ) < clusterRange xp := lt_of_lt_of_le hrx hrp
  have hWp : ln ≤ Real.log (2 ^ 13 * (T.side : ℝ) * (clusterRange xp : ℝ)) := by
    refine Real.log_le_log hn0 (le_trans hnear ?_)
    exact mul_le_mul_of_nonneg_left hrp (by positivity)
  have hdepth : m ≤ scaleDepthEnvelope D g d := by
    unfold scaleDepthEnvelope
    rw [← hxp, ← Real.log_div_log, le_div_iff₀ hlL, Real.log_div (by positivity) hd0.ne']
    linarith
  refine ⟨hdepth, ?_⟩
  have hm0 : 0 ≤ m := by
    rw [hmdef]
    have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
    linarith
  have hgap : D.lineGap (K - k) ≤ driftBound D (scaleDepthEnvelope D g d) := by
    unfold TrajectoryParameters.lineGap driftBound
    rw [hcast]
    have h1 : 3 * D.c₀ * m / (4 * D.X₀) ≤ 3 * D.c₀ * scaleDepthEnvelope D g d / (4 * D.X₀) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdepth (by positivity)) (by positivity)
    have h0 : 0 ≤ 3 * D.c₀ * m / (4 * D.X₀) := by positivity
    have h2 : Real.log (1 + 3 * D.c₀ * m / (4 * D.X₀)) ≤
        Real.log (1 + 3 * D.c₀ * scaleDepthEnvelope D g d / (4 * D.X₀)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 8 * D.Md / (3 * D.c₀))
    linarith
  obtain ⟨hl1, hl2⟩ := abs_le.mp hline
  have hbW := mul_le_mul_of_nonneg_left hWp hb.le
  have hxKpos : 0 < xK := lt_trans (by
    have : 0 < g ^ (-2 : ℤ) := by positivity
    exact this) hK
  have hH : heightBound D g d = D.threshold g + driftBound D (scaleDepthEnvelope D g d) +
      b * Real.log (2 ^ 13 * (T.side : ℝ) * (clusterRange xp : ℝ)) := rfl
  rw [hH, abs_le]
  constructor
  · linarith
  · linarith
private theorem envelopes_at_coupling {T : ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    (hD : D.Admissible) {g : ℝ} (hg0 : 0 < g) (hfl : inverseCouplingFloor D ≤ g ^ (-2 : ℤ))
    (hlev : ∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ) (β : ℝ), IsDatumAtDistance D g d K β →
      IsSeparatedAt (T.stepParameters y) β K d (separationLevel (T.stepParameters y) β K d) ∧
      separationLevel (T.stepParameters y) β K d < K ∧
      lengthInSites T.side K (separationLevel (T.stepParameters y) β K d) d ≤
        2 ^ 13 * (T.side : ℝ) *
          (clusterRange (D.coupling β (separationLevel (T.stepParameters y) β K d)) : ℝ))
    (hline : CouplingAlongLineAt D) (hpass : FirstPassageExistsAt D) :
    (∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ) (β : ℝ), IsDatumAtDistance D g d K β →
      lowerCouplingEnvelope D g d ≤ D.coupling β (separationLevel (T.stepParameters y) β K d) ∧
      D.coupling β (separationLevel (T.stepParameters y) β K d) ≤ upperCouplingEnvelope D g d ∧
      (K : ℝ) - separationLevel (T.stepParameters y) β K d ≤ scaleDepthEnvelope D g d ∧
      |logSlope * Real.log (1 / d) - D.coupling β (separationLevel (T.stepParameters y) β K d)| ≤
        heightBound D g d) ∧
    AntitoneOn (lowerCouplingEnvelope D g) (Set.Ioo 0 1) ∧
    AntitoneOn (upperCouplingEnvelope D g) (Set.Ioo 0 1) ∧
    (∀ d : ℝ, 0 < d → d < 1 → 8 < lowerCouplingEnvelope D g d) ∧
    BddAbove ((fun d => heightBound D g d / lowerCouplingEnvelope D g d) '' Set.Ioo 0 1) ∧
    Tendsto (fun d => heightBound D g d / lowerCouplingEnvelope D g d) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hL, hc, hX, hMd, hCr, hBs, hc0⟩ := admissible_basics D hD
  obtain ⟨hGy, hGX, hG9⟩ := inverseCouplingFloor_facts D hfl
  have hb := logSlope_pos
  have hu : ∀ d : ℝ, 0 < d → d < 1 → 0 < Real.log (1 / d) := fun d h0 h1 =>
    Real.log_pos (by rw [lt_div_iff₀ h0]; linarith)
  have hlogmono : ∀ d d' : ℝ, 0 < d → d ≤ d' → Real.log (1 / d') ≤ Real.log (1 / d) :=
    fun d d' h0 h =>
      Real.log_le_log (by have : 0 < d' := by linarith
                          positivity) (one_div_le_one_div_of_le h0 h)
  have hL1 : (1 : ℝ) < T.side := by linarith
  have hL0 : (0 : ℝ) < T.side := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd0 hd1 K β hdat
    have hw : β ∈ D.passageWindow K g := hdat.1
    obtain ⟨hfar, hlt, hnear⟩ := hlev d hd0 hd1 K β hdat
    have hpassK : ∃ K', IsFirstPassage D g β K' :=
      hpass g hg0 hGy β (show D.threshold g ≤ β from hw.1)
    obtain ⟨K', hK'⟩ := hpassK
    have hcut : SequencePassage.IsFirstPassageIndex D.shift g (D.coupling β) K := hw.2
    have hKK : K' = K := by
      rcases lt_trichotomy K' K with h | h | h
      · exact absurd hK'.isFirstPassageIndex.1 (not_le.mpr (hcut.2 K' h))
      · exact h
      · exact absurd hcut.1 (not_le.mpr (hK'.isFirstPassageIndex.2 K h))
    subst hKK
    have hKx : g ^ (-2 : ℤ) < D.coupling β K' := hK'.coupling_gt K' le_rfl
    have hl := hline g hg0 hGy K' β hw (separationLevel (T.stepParameters y) β K' d) hlt.le
    exact envelopes_at_level D hD hg0 hfl hd0 hd1 hw hlt hfar hnear hl hKx
  · intro d hd d' hd' hdd
    have h1 := mul_le_mul_of_nonneg_left (hlogmono d d' hd.1 hdd)
      (by positivity : 0 ≤ 3 / 4 * logSlope)
    unfold lowerCouplingEnvelope
    linarith
  · intro d hd d' hd' hdd
    have h1 := mul_le_mul_of_nonneg_left (hlogmono d d' hd.1 hdd)
      (by positivity : 0 ≤ 5 / 4 * logSlope)
    unfold upperCouplingEnvelope
    nlinarith
  · intro d hd0 hd1
    have h1 := mul_pos hb (hu d hd0 hd1)
    unfold lowerCouplingEnvelope
    rw [inv_sq_eq_zpow]
    nlinarith
  · have hX0 : 0 < D.X₀ := by linarith
    have hc0p : 0 < D.c₀ := by linarith
    have hΛ : 0 ≤ Real.log (2 ^ 13 * (T.side : ℝ)) := Real.log_nonneg (by nlinarith)
    have hlL : 0 < Real.log (T.side : ℝ) := Real.log_pos hL1
    have htop : 0 ≤ D.threshold g := by
      have : D.threshold g = g ^ (-2 : ℤ) + D.shift := rfl
      rw [this]
      linarith
    set Λ := Real.log (2 ^ 13 * (T.side : ℝ)) with hΛdef
    set P : ℝ := 2 * (D.threshold g + 2 * D.cH + 1 + 5 / 4 * logSlope * Λ) with hP
    have hP1 : 1 ≤ P := by
      have : 0 ≤ 5 / 4 * logSlope * Λ := by positivity
      rw [hP]
      linarith
    have hQ : (0 : ℝ) ≤ 5 / 2 * logSlope := by positivity
    have hup : ∀ d : ℝ, upperCouplingEnvelope D g d = P + 5 / 2 * logSlope * Real.log (1 / d) :=
      fun d => by
        unfold upperCouplingEnvelope
        rw [hP]
        ring
    obtain ⟨C₁, C₂, hC₁, hC₂, hH⟩ := height_le_log_bound P (5 / 2 * logSlope) Λ
      (Real.log (T.side : ℝ)) (3 * D.c₀ / (4 * D.X₀)) (8 * D.Md / (3 * D.c₀)) logSlope hP1 hQ hΛ
      hlL (by positivity) (by positivity) hb.le
    have hshape : ∀ d : ℝ, 0 < d → d < 1 →
        heightBound D g d = D.threshold g + 2 * D.cH + D.Cr +
          (8 * D.Md / (3 * D.c₀) * Real.log (1 + 3 * D.c₀ / (4 * D.X₀) *
            ((Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) + Real.log (1 / d)) /
              Real.log (T.side : ℝ))) +
          logSlope * (Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)))) ∧
        0 ≤ Real.log (clusterRange (upperCouplingEnvelope D g d)) ∧
        Real.log (clusterRange (upperCouplingEnvelope D g d)) ≤
          1 + Real.log (P + 5 / 2 * logSlope * Real.log (1 / d)) := by
      intro d hd0 hd1
      have hxp : 1 ≤ upperCouplingEnvelope D g d := by
        rw [hup]
        have := mul_nonneg hQ (hu d hd0 hd1).le
        linarith
      have hr1 := one_le_clusterRange (by linarith : 0 < upperCouplingEnvelope D g d)
      have hr0 : (0 : ℝ) < clusterRange (upperCouplingEnvelope D g d) := by linarith
      have hlw : Real.log (2 ^ 13 * (T.side : ℝ) * (clusterRange (upperCouplingEnvelope D g d) : ℝ)) =
          Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) :=
        Real.log_mul (by positivity) hr0.ne'
      have hdiv : Real.log (2 ^ 13 * (T.side : ℝ) *
            (clusterRange (upperCouplingEnvelope D g d) : ℝ) / d) =
          Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) + Real.log (1 / d) := by
        rw [Real.log_div (by positivity) hd0.ne', hlw, one_div, Real.log_inv]
        ring
      refine ⟨?_, Real.log_nonneg hr1, ?_⟩
      · unfold heightBound driftBound scaleDepthEnvelope
        rw [← Real.log_div_log, hdiv, hlw]
        have : 3 * D.c₀ * ((Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) +
              Real.log (1 / d)) / Real.log (T.side : ℝ)) / (4 * D.X₀) =
            3 * D.c₀ / (4 * D.X₀) *
              ((Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) + Real.log (1 / d)) /
                Real.log (T.side : ℝ)) := by
          ring
        rw [this]
        ring
      · have h1 := log_clusterRange_le hxp
        have h2 : 0 ≤ Real.log (upperCouplingEnvelope D g d) := Real.log_nonneg hxp
        rw [← hup]
        linarith
    have hlow : ∀ d : ℝ, 0 < d → d < 1 → D.threshold g + 2 * D.cH + D.Cr ≤ heightBound D g d := by
      intro d hd0 hd1
      obtain ⟨he, hρ0, -⟩ := hshape d hd0 hd1
      rw [he]
      have hu0 := hu d hd0 hd1
      have harg : 1 ≤ 1 + 3 * D.c₀ / (4 * D.X₀) *
          ((Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) + Real.log (1 / d)) /
            Real.log (T.side : ℝ)) := by
        have : 0 ≤ 3 * D.c₀ / (4 * D.X₀) *
          ((Λ + Real.log (clusterRange (upperCouplingEnvelope D g d)) + Real.log (1 / d)) /
            Real.log (T.side : ℝ)) := by
          positivity
        linarith
      have h1 := Real.log_nonneg harg
      have h2 : 0 ≤ 8 * D.Md / (3 * D.c₀) := by positivity
      have h3 := mul_nonneg h2 h1
      have h4 : 0 ≤ logSlope * (Λ + Real.log (clusterRange (upperCouplingEnvelope D g d))) := by
        positivity
      linarith
    have hhigh : ∀ d : ℝ, 0 < d → d < 1 → heightBound D g d ≤
        (D.threshold g + 2 * D.cH + D.Cr + C₁) + C₂ * Real.log (1 + Real.log (1 / d)) := by
      intro d hd0 hd1
      obtain ⟨he, hρ0, hρ⟩ := hshape d hd0 hd1
      have := hH (Real.log (1 / d)) _ (hu d hd0 hd1) hρ0 hρ
      rw [he]
      linarith
    have hAp : 0 < (g ^ 2)⁻¹ - 2 * D.cH := by
      rw [inv_sq_eq_zpow]
      linarith
    have hr := ratio_bounded_and_tendsto_zero (heightBound D g) (lowerCouplingEnvelope D g)
      (3 / 4 * logSlope) ((g ^ 2)⁻¹ - 2 * D.cH) (D.threshold g + 2 * D.cH + D.Cr)
      (D.threshold g + 2 * D.cH + D.Cr + C₁) C₂ (by positivity) hAp (by positivity) hC₂
      (fun d _ _ => rfl) hlow hhigh
    exact hr
theorem levelEnvelopes_of_separationLevel (h₁ : separationLevelStatement)
    (h₂ : couplingAlongLineStatement) (h₃ : firstPassageExistsStatement) :
    levelEnvelopesStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := h₁ a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hL T hTa hTL hDr hCS hOn hrtT hC => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hLo hL T hTa hTL hDr hCS hOn hrtT hC
  refine ⟨y₀, fun y hy0 hret hrow D hD g hg0 hfl => ?_⟩
  refine envelopes_at_coupling D hD hg0 hfl (fun d h0 h1 K β hdat => ?_) (h₂ T y D hD) (h₃ T y D hD)
  obtain ⟨hg, hlt, hnear⟩ := hy y hy0 hret hrow D hD g hg0 hfl d h0 h1 K β hdat
  exact ⟨hg.1.2, hlt, hnear⟩
end YangMills.Construction.SystemOfAdmissibleConstants
end
