import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.ResponseInTheExpansion.LocalRadii
def mirrorHalfSide (x : ℝ) : ℕ := ⌊x ^ ((1 : ℝ) / 20)⌋₊ / 2
theorem eventually_radii_ordered (A σ c : ℝ) (hσ : 0 < σ) (hc : 0 < c) : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    A ≤ logCubeScale x ∧ logCubeScale x + 1 ≤ mirrorHalfSide x ∧ (TorusLumps.clusterRange x : ℝ) / 64 ≤ mirrorHalfSide x ∧
    12 * x ^ ((1 : ℝ) / 90) + mirrorHalfSide x ≤ localBoxRadius x ∧ 20 * x ^ (-(1 / 4 : ℝ)) ≤ σ ∧
    Real.exp (-(c * logCubeScale x)) ≤ x ^ (-2 : ℝ) := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 3 ≤ (1 / 4) * x ^ ((1 : ℝ) / 20) := by
    have h := isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 20)
    have h' := h.def (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [h', eventually_gt_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have e : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hx
    exact hx
  have h2 : ∀ B : ℝ, ∀ᶠ x : ℝ in atTop, B ≤ x ^ ((7 : ℝ) / 180) := fun B =>
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 180)).eventually_ge_atTop B
  have h3 : ∀ᶠ x : ℝ in atTop, 16 ≤ x ^ ((1 : ℝ) / 20) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually_ge_atTop 16
  have h4 : ∀ᶠ x : ℝ in atTop, x ^ (-(1 / 4 : ℝ)) ≤ σ / 20 := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4))
    exact this.eventually_le_const (by positivity)
  have h5 : ∀ B : ℝ, ∀ᶠ x : ℝ in atTop, B ≤ Real.log x := fun B => hlog.eventually_ge_atTop B
  have hT : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ A + 1 ≤ T₀ ∧ c ≤ 2 * T₀ ∧ 4 ≤ c * T₀ ^ 2 := by
    refine ⟨max (max 1 (A + 1)) (max c (4 / c + 1)), ?_, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · have a1 : c ≤ max (max 1 (A + 1)) (max c (4 / c + 1)) := (le_max_left _ _).trans (le_max_right _ _)
      have a2 : 1 ≤ max (max 1 (A + 1)) (max c (4 / c + 1)) := (le_max_left _ _).trans (le_max_left _ _)
      linarith
    · have a1 : 4 / c + 1 ≤ max (max 1 (A + 1)) (max c (4 / c + 1)) := (le_max_right _ _).trans (le_max_right _ _)
      have a2 : 1 ≤ max (max 1 (A + 1)) (max c (4 / c + 1)) := (le_max_left _ _).trans (le_max_left _ _)
      set T := max (max 1 (A + 1)) (max c (4 / c + 1))
      have a3 : c * (4 / c) = 4 := by field_simp
      have a4 : c * (4 / c + 1) ≤ c * T := mul_le_mul_of_nonneg_left a1 hc.le
      have a5 : 4 ≤ c * T := by nlinarith
      nlinarith
  obtain ⟨T₀, hT1, hTA, hTc, hTc2⟩ := hT
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (h1.and ((h2 48).and (h3.and (h4.and ((h5 T₀).and (eventually_ge_atTop 1))))))
  refine ⟨max x₀ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx₀ x ((le_max_left _ _).trans hx)
  have hxpos : 0 < x := by linarith
  set t := Real.log x with ht
  set w := x ^ ((1 : ℝ) / 20) with hw
  have ht1 : 1 ≤ t := hT1.trans a5
  have hfl := Nat.floor_le (show 0 ≤ t ^ 3 by positivity)
  have hfl' := Nat.lt_floor_add_one (t ^ 3)
  have hw0 : 0 ≤ w := by positivity
  have hwl := Nat.floor_le hw0
  have hwl' := Nat.lt_floor_add_one w
  have hh : mirrorHalfSide x = ⌊w⌋₊ / 2 := rfl
  have hhalf1 : (mirrorHalfSide x : ℝ) ≤ w / 2 := by
    have : 2 * mirrorHalfSide x ≤ ⌊w⌋₊ := by
      rw [hh]
      omega
    have : (2 : ℝ) * mirrorHalfSide x ≤ ⌊w⌋₊ := by exact_mod_cast this
    linarith
  have hhalf2 : w / 2 - 1 ≤ (mirrorHalfSide x : ℝ) := by
    have : ⌊w⌋₊ ≤ 2 * mirrorHalfSide x + 1 := by
      rw [hh]
      omega
    have : (⌊w⌋₊ : ℝ) ≤ 2 * mirrorHalfSide x + 1 := by exact_mod_cast this
    linarith
  have hS : logCubeScale x = (⌊t ^ 3⌋₊ : ℝ) := rfl
  have hLr : localBoxRadius x = (⌊w⌋₊ : ℝ) := rfl
  have hx1 : 1 ≤ x := a6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS]
    have : t ≤ t ^ 3 := by nlinarith [sq_nonneg t, sq_nonneg (t - 1)]
    linarith
  · rw [hS]
    linarith
  · have hc1 : (TorusLumps.clusterRange x : ℝ) ≤ x ^ ((1 : ℝ) / 100) + 1 := by
      unfold TorusLumps.clusterRange
      have := Nat.ceil_lt_add_one (show 0 ≤ x ^ ((1 : ℝ) / 100) by positivity)
      exact this.le
    have hc2 : x ^ ((1 : ℝ) / 100) ≤ w := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    linarith
  · rw [hLr]
    have e1 : w = x ^ ((1 : ℝ) / 90) * x ^ ((7 : ℝ) / 180) := by
      rw [hw, ← Real.rpow_add hxpos]
      norm_num
    have e2 : 1 ≤ x ^ ((1 : ℝ) / 90) := Real.one_le_rpow hx1 (by norm_num)
    have e3 : 48 * x ^ ((1 : ℝ) / 90) ≤ w := by
      rw [e1]
      nlinarith
    linarith
  · linarith [a4, (show 0 < σ by exact hσ)]
  · rw [hS, Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    have b1 : t ^ 3 - 1 ≤ (⌊t ^ 3⌋₊ : ℝ) := by linarith
    have b2 : T₀ ≤ t := a5
    have b3 : 4 ≤ c * t ^ 2 := by
      have : T₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) b2 2
      nlinarith
    nlinarith
section Moment
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
theorem lintegral_indicator_pow_le_of_cube_bound {S Loc : Set Ω} {f A : Ω → ℝ} {b X₀ Y : ℝ} (q : ℕ) (hq : 1 ≤ q) (hb : 0 ≤ b) (hX₀ : 0 ≤ X₀) (hY : 0 ≤ Y)
    (hSL : S ⊆ Loc) (hf : ∀ᵐ u ∂μ, u ∈ S → |f u| ≤ b * (|A u| ^ 3 + X₀))
    (hi : Integrable (Loc.indicator fun u => A u ^ (6 * q)) μ)
    (hm : ∫ u, Loc.indicator (fun u => A u ^ (6 * q)) u ∂μ ≤ Y ^ (6 * q))
    (hi0 : Integrable (Loc.indicator fun u => A u ^ 0) μ)
    (hm0 : ∫ u, Loc.indicator (fun u => A u ^ 0) u ∂μ ≤ 1) :
    ∫⁻ u, ENNReal.ofReal (S.indicator (fun u => |f u| ^ (2 * q)) u) ∂μ ≤
      ENNReal.ofReal ((2 * b * (Y ^ 3 + X₀)) ^ (2 * q)) := by
  set c₁ := (2 * b) ^ (2 * q) with hc₁
  set c₂ := (2 * b * X₀) ^ (2 * q) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set g : Ω → ℝ := fun u => c₁ * Loc.indicator (fun u => A u ^ (6 * q)) u + c₂ * Loc.indicator (fun u => A u ^ 0) u with hg
  have hgi : Integrable g μ := (hi.const_mul c₁).add (hi0.const_mul c₂)
  have hg0 : ∀ u, 0 ≤ g u := by
    intro u
    have e1 : 0 ≤ Loc.indicator (fun u => A u ^ (6 * q)) u := by
      refine Set.indicator_nonneg (fun u _ => ?_) u
      have : A u ^ (6 * q) = (A u ^ (3 * q)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      rw [this]
      positivity
    have e2 : 0 ≤ Loc.indicator (fun u => A u ^ 0) u :=
      Set.indicator_nonneg (fun u _ => by simp) u
    exact add_nonneg (mul_nonneg hc₁0 e1) (mul_nonneg hc₂0 e2)
  have hle : ∀ᵐ u ∂μ, ENNReal.ofReal (S.indicator (fun u => |f u| ^ (2 * q)) u) ≤ ENNReal.ofReal (g u) := by
    filter_upwards [hf] with u hu
    apply ENNReal.ofReal_le_ofReal
    by_cases hS : u ∈ S
    · have hL : u ∈ Loc := hSL hS
      rw [Set.indicator_of_mem hS]
      simp only [hg]
      rw [Set.indicator_of_mem hL, Set.indicator_of_mem hL, pow_zero, mul_one]
      have a0 : 0 ≤ |A u| ^ 3 := by positivity
      have h1 : |f u| ^ (2 * q) ≤ (b * (|A u| ^ 3 + X₀)) ^ (2 * q) :=
        pow_le_pow_left₀ (abs_nonneg _) (hu hS) _
      have h2 : (|A u| ^ 3 + X₀) ^ (2 * q) ≤ 2 ^ (2 * q) * ((|A u| ^ 3) ^ (2 * q) + X₀ ^ (2 * q)) := by
        rcases le_total (|A u| ^ 3) X₀ with hl | hl
        · have : (|A u| ^ 3 + X₀) ^ (2 * q) ≤ (2 * X₀) ^ (2 * q) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
          rw [mul_pow] at this
          have : 0 ≤ (|A u| ^ 3) ^ (2 * q) := by positivity
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (2 * q)]
        · have : (|A u| ^ 3 + X₀) ^ (2 * q) ≤ (2 * |A u| ^ 3) ^ (2 * q) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
          rw [mul_pow] at this
          have : 0 ≤ X₀ ^ (2 * q) := by positivity
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (2 * q)]
      have e3 : (|A u| ^ 3) ^ (2 * q) = A u ^ (6 * q) := by
        rw [← pow_mul, show 3 * (2 * q) = 6 * q by ring]
        exact Even.pow_abs ⟨3 * q, by ring⟩ _
      rw [e3] at h2
      calc |f u| ^ (2 * q) ≤ (b * (|A u| ^ 3 + X₀)) ^ (2 * q) := h1
        _ = b ^ (2 * q) * (|A u| ^ 3 + X₀) ^ (2 * q) := mul_pow _ _ _
        _ ≤ b ^ (2 * q) * (2 ^ (2 * q) * (A u ^ (6 * q) + X₀ ^ (2 * q))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = c₁ * A u ^ (6 * q) + c₂ := by
            rw [hc₁, hc₂, mul_pow, mul_pow, mul_pow]
            ring
    · rw [Set.indicator_of_notMem hS]
      exact hg0 u
  calc ∫⁻ u, ENNReal.ofReal (S.indicator (fun u => |f u| ^ (2 * q)) u) ∂μ
      ≤ ∫⁻ u, ENNReal.ofReal (g u) ∂μ := lintegral_mono_ae hle
    _ = ENNReal.ofReal (∫ u, g u ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)).symm
    _ ≤ ENNReal.ofReal ((2 * b * (Y ^ 3 + X₀)) ^ (2 * q)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : ∫ u, g u ∂μ = c₁ * ∫ u, Loc.indicator (fun u => A u ^ (6 * q)) u ∂μ +
            c₂ * ∫ u, Loc.indicator (fun u => A u ^ 0) u ∂μ := by
          simp only [hg]
          rw [integral_add (hi.const_mul c₁) (hi0.const_mul c₂), integral_const_mul, integral_const_mul]
        rw [e]
        have h1 := mul_le_mul_of_nonneg_left hm hc₁0
        have h2 := mul_le_mul_of_nonneg_left hm0 hc₂0
        have h3 : Y ^ (6 * q) = (Y ^ 3) ^ (2 * q) := by
          rw [← pow_mul]
          congr 1
          ring
        have h4 : (Y ^ 3) ^ (2 * q) + X₀ ^ (2 * q) ≤ (Y ^ 3 + X₀) ^ (2 * q) :=
          pow_add_pow_le (by positivity) hX₀ (by omega)
        have h5 : (2 * b * (Y ^ 3 + X₀)) ^ (2 * q) = c₁ * (Y ^ 3 + X₀) ^ (2 * q) := by
          rw [hc₁, mul_pow]
        have h6 : c₂ = c₁ * X₀ ^ (2 * q) := by
          rw [hc₂, hc₁, mul_pow]
        rw [h5]
        rw [h3] at h1
        have h7 := mul_le_mul_of_nonneg_left h4 hc₁0
        nlinarith
end Moment
theorem ae_exists_small_near_abs {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {Loc : Ω → Prop} {Small Desc : ℝ → Ω → Prop} {A : Ω → ℝ}
    {x₄ δ : ℝ} (hx₄ : 0 < x₄) (hx₄1 : x₄ ≤ 1) (hδ : 0 < δ)
    (h1 : ∀ s : ℝ, s < 1 → ∀ᵐ u ∂μ, Loc u → A u ≤ s → Small s u)
    (h2 : ∀ s : ℝ, 0 ≤ s → s ≤ x₄ → ∀ᵐ u ∂μ, Loc u → Small s u → Desc s u) :
    ∀ᵐ u ∂μ, Loc u → Small x₄ u → ∃ s : ℝ, 0 ≤ s ∧ s ≤ x₄ ∧ s ≤ |A u| + δ ∧ Small s u ∧ Desc s u := by
  have e1 := (ae_all_iff (ι := {r : ℚ // (r : ℝ) < 1})).mpr fun r => h1 r r.2
  have e2 := (ae_all_iff (ι := {r : ℚ // 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ x₄})).mpr fun r => h2 r r.2.1 r.2.2
  have e3 := h2 x₄ hx₄.le le_rfl
  filter_upwards [e1, e2, e3] with u a1 a2 a3 hloc hsm
  by_cases hcase : |A u| + δ ≤ x₄
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show |A u| < |A u| + δ by linarith)
    have hr0 : 0 ≤ (r : ℝ) := (abs_nonneg _).trans hr1.le
    have hrle : (r : ℝ) ≤ x₄ := hr2.le.trans hcase
    have hsr := a1 ⟨r, lt_of_lt_of_le hr2 (hcase.trans hx₄1)⟩ hloc ((le_abs_self _).trans hr1.le)
    exact ⟨r, hr0, hrle, hr2.le, hsr, a2 ⟨r, hr0, hrle⟩ hloc hsr⟩
  · push Not at hcase
    exact ⟨x₄, hx₄.le, le_rfl, hcase.le, hsm, a3 hloc hsm⟩
end YangMills.Construction.ResponseInTheExpansion.LocalRadii
end
