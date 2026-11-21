import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.LawByMomentsOfTheFlow.ColdFineField
import YangMills.Construction.LawByMomentsOfTheFlow.ColoursOfForms
import YangMills.Construction.LawByMomentsOfTheFlow.CurlOfTheCutOverAReference
import YangMills.Construction.LawByMomentsOfTheFlow.FramesNearAtAPoint
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongAList
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheColdGround
import YangMills.Construction.LawByMomentsOfTheFlow.PagesJoin
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
open BlockAverages MomentMethod TorusFields StepSettings ResponseInTheExpansion
namespace MomentLaw
namespace ColdFineFieldAux
section Numbers
private theorem bound_linear_aux {d v y ω b B Pl l : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (hy : 0 ≤ y) (hω : 0 ≤ ω) (hωy : ω ≤ y) (hB : 0 ≤ B)
    (hb : b = B * y) (hPl0 : 0 ≤ Pl) (hPl : Pl ≤ 16 * d + 20) (hl : l = 4) :
    (d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b ≤ (2 + 28 * B) * ((1 + d) * (v + y)) := by
  subst hb hl
  have h1 : (d + 2) * (v + ω) ≤ 2 * ((1 + d) * (v + y)) := by
    have a1 : d + 2 ≤ 2 * (1 + d) := by linarith
    have a2 : (d + 2) * (v + ω) ≤ 2 * (1 + d) * (v + y) := mul_le_mul a1 (by linarith) (by positivity) (by positivity)
    linarith
  have hBy : 0 ≤ B * y := by positivity
  have h2 : (d + 2) * (4 * (B * y)) ≤ 8 * ((1 + d) * (B * y)) := by
    have : (d + 2) * (4 * (B * y)) ≤ (2 * (1 + d)) * (4 * (B * y)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have h3 : Pl * (B * y) ≤ 20 * ((1 + d) * (B * y)) := by
    have : Pl * (B * y) ≤ (20 * (1 + d)) * (B * y) := mul_le_mul_of_nonneg_right (by linarith) hBy
    linarith
  have h4 : (1 + d) * (B * y) ≤ B * ((1 + d) * (v + y)) := by
    have h5 : 0 ≤ B * (1 + d) := by positivity
    have : B * (1 + d) * y ≤ B * (1 + d) * (v + y) := mul_le_mul_of_nonneg_left (by linarith) h5
    calc (1 + d) * (B * y) = B * (1 + d) * y := by ring
      _ ≤ B * (1 + d) * (v + y) := this
      _ = _ := by ring
  have e : (2 + 28 * B) * ((1 + d) * (v + y)) = 2 * ((1 + d) * (v + y)) + 28 * (B * ((1 + d) * (v + y))) := by ring
  rw [e]
  linarith
private theorem bound_curl_aux {K d v y ω b B Pl l t T : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d) (hv : 0 ≤ v) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hω : 0 ≤ ω)
    (hωy : ω ≤ y ^ 2) (hB : 0 ≤ B) (hb : b = B * y) (hPl0 : 0 ≤ Pl) (hPl : Pl ≤ 16 * d + 20) (hl : l = 4) (ht : t ≤ T * y ^ 2)
    (hT : 0 ≤ T) :
    K * ((d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b) ^ 2 + 4 * ω +
        0 * ((d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b) + 0 * (l * b) + 20 * (Pl * t) ≤
      (K * (2 + 28 * B) ^ 2 + 4 + 400 * T) * (1 + d) ^ 2 * (v + y) ^ 2 := by
  have hy2 : y ^ 2 ≤ y := by nlinarith
  have hU := bound_linear_aux hd hv hy hω (hωy.trans hy2) hB hb hPl0 hPl hl
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hl0 : 0 ≤ l := by rw [hl]; norm_num
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (1 + d) * (v + y) := ⟨_, rfl⟩
  rw [← hw] at hU
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hyw : y ≤ w := by
    rw [hw]
    nlinarith [mul_nonneg hd hv, mul_nonneg hd hy]
  have hU0 : 0 ≤ (d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b := by positivity
  have h1 : ((d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b) ^ 2 ≤ (2 + 28 * B) ^ 2 * w ^ 2 := by
    calc _ ≤ ((2 + 28 * B) * w) ^ 2 := pow_le_pow_left₀ hU0 hU 2
      _ = _ := by ring
  have h2 : y ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hy hyw 2
  have h3 : (1 + d) * y ^ 2 ≤ w ^ 2 := by
    rw [hw]
    have a1 : (1 + d) ≤ (1 + d) ^ 2 := by nlinarith
    have a2 : y ^ 2 ≤ (v + y) ^ 2 := pow_le_pow_left₀ hy (by linarith) 2
    calc (1 + d) * y ^ 2 ≤ (1 + d) ^ 2 * (v + y) ^ 2 := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = _ := by ring
  have h4 : 20 * (Pl * t) ≤ 400 * T * w ^ 2 := by
    have a1 : Pl ≤ 20 * (1 + d) := by linarith
    have a0 : t ≤ T * y ^ 2 := ht
    have a2 : Pl * t ≤ 20 * (1 + d) * (T * y ^ 2) :=
      (mul_le_mul_of_nonneg_left a0 hPl0).trans (mul_le_mul_of_nonneg_right a1 (by positivity))
    have a3 : 20 * (1 + d) * (T * y ^ 2) = 20 * T * ((1 + d) * y ^ 2) := by ring
    rw [a3] at a2
    have a4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 20 * T)
    nlinarith
  have e : (K * (2 + 28 * B) ^ 2 + 4 + 400 * T) * (1 + d) ^ 2 * (v + y) ^ 2 =
      K * ((2 + 28 * B) ^ 2 * w ^ 2) + 4 * w ^ 2 + 400 * T * w ^ 2 := by
    rw [hw]
    ring
  rw [e]
  have h5 := mul_le_mul_of_nonneg_left h1 hK
  linarith
private theorem bound_cut_aux {K d v y ω b B Pl l t T m1 : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d) (hv : 0 ≤ v) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hω : 0 ≤ ω)
    (hωy : ω ≤ y ^ 2) (hB : 0 ≤ B) (hb : b = B * y) (hPl0 : 0 ≤ Pl) (hPl : Pl ≤ 16 * d + 20) (hl : l = 4) (ht : t ≤ T * y ^ 2)
    (hT : 0 ≤ T) (hm1 : 0 < m1) (hdm : 1 + d ≤ 5 * m1) (hsq : (1 + d) ^ 2 * (v + y) ≤ 1) :
    K * ((d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b) ^ 2 + (4 * ω + v / 16) +
        124 / m1 * ((d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b) + 1 * (l * b) + 20 * (Pl * t) ≤
      (K * (2 + 28 * B) ^ 2 + 620 * (2 + 28 * B) + 5 + 4 * B + 400 * T) * (v + y) := by
  have hy2 : y ^ 2 ≤ y := by nlinarith
  have hU := bound_linear_aux hd hv hy hω (hωy.trans hy2) hB hb hPl0 hPl hl
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hl0 : 0 ≤ l := by rw [hl]; norm_num
  have hU0 : 0 ≤ (d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b := by positivity
  obtain ⟨U, hUd⟩ : ∃ U : ℝ, U = (d + 2) * (v + ω) + (d + 2) * (l * b) + Pl * b := ⟨_, rfl⟩
  rw [← hUd] at hU hU0 ⊢
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 + 28 * B := ⟨_, rfl⟩
  rw [← hC₁] at hU ⊢
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hvy : 0 ≤ v + y := by positivity
  have h1 : U ^ 2 ≤ C₁ ^ 2 * (v + y) := by
    calc U ^ 2 ≤ (C₁ * ((1 + d) * (v + y))) ^ 2 := pow_le_pow_left₀ hU0 hU 2
      _ = C₁ ^ 2 * ((1 + d) ^ 2 * (v + y) * (v + y)) := by ring
      _ ≤ C₁ ^ 2 * (1 * (v + y)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hsq hvy
      _ = _ := by ring
  have h2 : 124 / m1 * U ≤ 620 * C₁ * (v + y) := by
    have a1 : U ≤ C₁ * (5 * m1 * (v + y)) := by
      refine hU.trans (mul_le_mul_of_nonneg_left ?_ hC₁0)
      exact mul_le_mul_of_nonneg_right hdm hvy
    have a2 : 124 / m1 * U ≤ 124 / m1 * (C₁ * (5 * m1 * (v + y))) := mul_le_mul_of_nonneg_left a1 (by positivity)
    have e : 124 / m1 * (C₁ * (5 * m1 * (v + y))) = 620 * C₁ * (v + y) := by
      field_simp
      ring
    linarith
  have h4 : 1 * (l * b) ≤ 4 * B * (v + y) := by
    rw [hl, hb]
    have : B * y ≤ B * (v + y) := mul_le_mul_of_nonneg_left (by linarith) hB
    linarith
  have h5 : 20 * (Pl * t) ≤ 400 * T * (v + y) := by
    have a1 : (1 + d) * y ≤ 1 := by
      have a2 : (1 + d) ≤ (1 + d) ^ 2 := by nlinarith
      have a3 : (1 + d) * y ≤ (1 + d) ^ 2 * (v + y) := mul_le_mul a2 (by linarith) hy (by positivity)
      linarith
    have a4 : (1 + d) * y ^ 2 ≤ y := by
      have := mul_le_mul_of_nonneg_right a1 hy
      calc (1 + d) * y ^ 2 = (1 + d) * y * y := by ring
        _ ≤ 1 * y := this
        _ = y := one_mul y
    have a5 : Pl ≤ 20 * (1 + d) := by linarith
    have a6 : Pl * t ≤ 20 * (1 + d) * (T * y ^ 2) :=
      (mul_le_mul_of_nonneg_left ht hPl0).trans (mul_le_mul_of_nonneg_right a5 (by positivity))
    have a7 : 20 * (1 + d) * (T * y ^ 2) = 20 * T * ((1 + d) * y ^ 2) := by ring
    rw [a7] at a6
    have a8 := mul_le_mul_of_nonneg_left a4 (by positivity : 0 ≤ 20 * T)
    have a9 : 20 * T * y ≤ 20 * T * (v + y) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have e : (K * C₁ ^ 2 + 620 * C₁ + 5 + 4 * B + 400 * T) * (v + y) =
      K * (C₁ ^ 2 * (v + y)) + 620 * C₁ * (v + y) + 5 * (v + y) + 4 * B * (v + y) + 400 * T * (v + y) := by ring
  rw [e]
  have h6 := mul_le_mul_of_nonneg_left h1 hK
  linarith
private theorem exists_large_scale (G κ σ : ℝ) (hG : 0 ≤ G) (hκ : 0 ≤ κ) (hσ : 0 < σ) :
    ∃ Z₀ : ℝ, 200 ≤ Z₀ ∧ ∀ z m v : ℝ, Z₀ ≤ z → 0 ≤ m → m ≤ 4 * z ^ 2 → 0 ≤ v → v ≤ (z ^ 25)⁻¹ →
      10 ^ 4 * G ^ 2 * (2 * m + 6 + 3) ^ 2 * (v + (z ^ 200)⁻¹ + 100 * (2 * m + 6 + 3) * (z ^ 30)⁻¹) ≤ 1 ∧
      κ * ((2 * m + 6 + 1) * v) ≤ 1 / 64 ∧ 2 * (2 * m + 6) + 2 < z ^ 50 ∧
      v / 2 + 8 * (z ^ 30)⁻¹ + 5 * (z ^ 200)⁻¹ ≤ (z ^ 25)⁻¹ ∧ 64 * (z ^ 25)⁻¹ < σ ∧
      (1 + 2 * m) ^ 2 * (v + (z ^ 50)⁻¹) ≤ 1 := by
  obtain ⟨Gc, hGc⟩ : ∃ Gc : ℝ, Gc = 10 ^ 4 * G ^ 2 * 289 * 1702 := ⟨_, rfl⟩
  have hGc0 : 0 ≤ Gc := by rw [hGc]; positivity
  refine ⟨Gc + 64 * 17 * κ + 64 / σ + 200, ?_, fun z m v hz hm0 hm hv0 hv => ?_⟩
  · have : 0 ≤ 64 / σ := by positivity
    have h2 : 0 ≤ 64 * 17 * κ := by positivity
    linarith
  have h64 : 0 ≤ 64 / σ := by positivity
  have hz200 : 200 ≤ z := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = z⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hzu : z * u = 1 := by rw [hu]; field_simp
  have hu1 : u ≤ 1 / 200 := by
    have : 200 * u ≤ z * u := mul_le_mul_of_nonneg_right hz200 hu0.le
    rw [hzu] at this
    linarith
  have hul : u ≤ 1 := by linarith
  have inv : ∀ k : ℕ, (z ^ k)⁻¹ = u ^ k := fun k => by rw [hu, inv_pow]
  rw [inv 25, inv 200, inv 30, inv 50]
  rw [inv 25] at hv
  have pw : ∀ a b : ℕ, b ≤ a → u ^ a ≤ u ^ b := fun a b h => pow_le_pow_of_le_one hu0.le hul h
  have hz2 : 1 ≤ z ^ 2 := by nlinarith
  have hz20 : 0 < z ^ 2 := by positivity
  have hA : 2 * m + 6 + 3 ≤ 17 * z ^ 2 := by linarith
  have hA0 : 0 ≤ 2 * m + 6 + 3 := by positivity
  have e2 : ∀ k : ℕ, z ^ 2 * u ^ (k + 2) = u ^ k := fun k => by
    calc z ^ 2 * u ^ (k + 2) = (z * u) ^ 2 * u ^ k := by ring
      _ = u ^ k := by rw [hzu]; ring
  have e4 : ∀ k : ℕ, z ^ 4 * u ^ (k + 4) = u ^ k := fun k => by
    calc z ^ 4 * u ^ (k + 4) = (z * u) ^ 4 * u ^ k := by ring
      _ = u ^ k := by rw [hzu]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : 100 * (2 * m + 6 + 3) * u ^ 30 ≤ 1700 * u ^ 25 := by
      have a1 : (2 * m + 6 + 3) * u ^ 30 ≤ 17 * z ^ 2 * u ^ 30 := mul_le_mul_of_nonneg_right hA (by positivity)
      have a2 : 17 * z ^ 2 * u ^ 30 = 17 * u ^ 28 := by
        have := e2 28
        calc 17 * z ^ 2 * u ^ 30 = 17 * (z ^ 2 * u ^ (28 + 2)) := by ring
          _ = _ := by rw [this]
      have a3 := pw 28 25 (by norm_num)
      nlinarith
    have h2 : v + u ^ 200 + 100 * (2 * m + 6 + 3) * u ^ 30 ≤ 1702 * u ^ 25 := by
      have := pw 200 25 (by norm_num)
      linarith
    have h3 : (2 * m + 6 + 3) ^ 2 ≤ 289 * z ^ 4 := by
      calc (2 * m + 6 + 3) ^ 2 ≤ (17 * z ^ 2) ^ 2 := pow_le_pow_left₀ hA0 hA 2
        _ = _ := by ring
    have h4 : 0 ≤ v + u ^ 200 + 100 * (2 * m + 6 + 3) * u ^ 30 := by positivity
    have h5 : (2 * m + 6 + 3) ^ 2 * (v + u ^ 200 + 100 * (2 * m + 6 + 3) * u ^ 30) ≤ 289 * z ^ 4 * (1702 * u ^ 25) :=
      mul_le_mul h3 h2 h4 (by positivity)
    have h6 : 289 * z ^ 4 * (1702 * u ^ 25) = 289 * 1702 * u ^ 21 := by
      have := e4 21
      calc 289 * z ^ 4 * (1702 * u ^ 25) = 289 * 1702 * (z ^ 4 * u ^ (21 + 4)) := by ring
        _ = _ := by rw [this]
    have h7 : u ^ 21 ≤ u := by
      have := pw 21 1 (by norm_num)
      simpa using this
    have h8 : 10 ^ 4 * G ^ 2 * (2 * m + 6 + 3) ^ 2 * (v + u ^ 200 + 100 * (2 * m + 6 + 3) * u ^ 30) ≤ Gc * u := by
      have h9 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 10 ^ 4 * G ^ 2)
      rw [h6] at h9
      have h10 : 10 ^ 4 * G ^ 2 * (289 * 1702 * u ^ 21) ≤ 10 ^ 4 * G ^ 2 * (289 * 1702 * u) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [hGc]
      calc _ = 10 ^ 4 * G ^ 2 * ((2 * m + 6 + 3) ^ 2 * (v + u ^ 200 + 100 * (2 * m + 6 + 3) * u ^ 30)) := by ring
        _ ≤ _ := h9.trans h10
        _ = _ := by ring
    refine h8.trans ?_
    have : Gc * u ≤ z * u := mul_le_mul_of_nonneg_right (by linarith) hu0.le
    rw [hzu] at this
    exact this
  · have h1 : (2 * m + 6 + 1) * v ≤ 17 * z ^ 2 * u ^ 25 :=
      mul_le_mul (by linarith) hv hv0 (by positivity)
    have h2 : 17 * z ^ 2 * u ^ 25 = 17 * u ^ 23 := by
      have := e2 23
      calc 17 * z ^ 2 * u ^ 25 = 17 * (z ^ 2 * u ^ (23 + 2)) := by ring
        _ = _ := by rw [this]
    have h3 : u ^ 23 ≤ u := by
      have := pw 23 1 (by norm_num)
      simpa using this
    have h4 : (2 * m + 6 + 1) * v ≤ 17 * u := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hκ
    have h6 : 64 * 17 * κ * u ≤ z * u := mul_le_mul_of_nonneg_right (by linarith) hu0.le
    rw [hzu] at h6
    nlinarith
  · have h1 : 2 * (2 * m + 6) + 2 ≤ 30 * z ^ 2 := by linarith
    have h2 : z ^ 3 ≤ z ^ 50 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h3 : 200 * z ^ 2 ≤ z * z ^ 2 := mul_le_mul_of_nonneg_right hz200 hz20.le
    have e : z * z ^ 2 = z ^ 3 := by ring
    rw [e] at h3
    linarith
  · have a1 := pw 200 30 (by norm_num)
    have a2 : u ^ 30 = u ^ 5 * u ^ 25 := by ring
    have a3 : u ^ 5 ≤ u := by
      have := pw 5 1 (by norm_num)
      simpa using this
    have a4 : 0 ≤ u ^ 25 := by positivity
    have a5 : u ^ 5 * u ^ 25 ≤ 1 / 200 * u ^ 25 := mul_le_mul_of_nonneg_right (a3.trans hu1) a4
    linarith
  · have a1 : u ^ 25 ≤ u := by
      have := pw 25 1 (by norm_num)
      simpa using this
    have a2 : 64 / σ < z := by linarith
    rw [div_lt_iff₀ hσ] at a2
    have a3 : 64 * u < z * σ * u := mul_lt_mul_of_pos_right a2 hu0
    have a4 : z * σ * u = σ := by
      calc z * σ * u = (z * u) * σ := by ring
        _ = σ := by rw [hzu, one_mul]
    linarith
  · have h1 : 1 + 2 * m ≤ 9 * z ^ 2 := by linarith
    have h2 : (1 + 2 * m) ^ 2 ≤ 81 * z ^ 4 := by
      calc (1 + 2 * m) ^ 2 ≤ (9 * z ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = _ := by ring
    have h3 : v + u ^ 50 ≤ 2 * u ^ 25 := by
      have := pw 50 25 (by norm_num)
      linarith
    have h4 : (1 + 2 * m) ^ 2 * (v + u ^ 50) ≤ 81 * z ^ 4 * (2 * u ^ 25) :=
      mul_le_mul h2 h3 (by positivity) (by positivity)
    have h5 : 81 * z ^ 4 * (2 * u ^ 25) = 162 * u ^ 21 := by
      have := e4 21
      calc 81 * z ^ 4 * (2 * u ^ 25) = 162 * (z ^ 4 * u ^ (21 + 4)) := by ring
        _ = _ := by rw [this]
    have h7 : u ^ 21 ≤ u := by
      have := pw 21 1 (by norm_num)
      simpa using this
    linarith
private theorem exists_log_le_half (Cv : ℝ) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → |Cv| * Real.log x ≤ x / 2 := by
  have h := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / (2 * (|Cv| + 1)) by positivity)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨max x₁ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨a1, a2⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg a2
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at a1
  have hp : (0 : ℝ) < |Cv| + 1 := by positivity
  have h2 : (|Cv| + 1) * Real.log x ≤ x / 2 := by
    have := mul_le_mul_of_nonneg_left a1 hp.le
    have e : (|Cv| + 1) * (1 / (2 * (|Cv| + 1)) * x) = x / 2 := by
      field_simp
    linarith
  nlinarith
private theorem rpow_neg_div_hundred (x : ℝ) (hx : 0 < x) (k : ℕ) : x ^ (-((k : ℝ) / 100)) = ((x ^ ((1 : ℝ) / 100)) ^ k)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_neg hx.le]
  congr 1
  ring
private theorem tail_count_le {z m x Cm : ℝ} (k N : ℕ) (hk : k = 5 * N + 10) (hz : 1 ≤ z) (hx : x = z ^ 100) (hm0 : 0 ≤ m) (hm : m ≤ 4 * z ^ 2) (hC : 0 ≤ Cm) (xu : ℝ)
    (hxu : x / 2 ≤ xu) : (4 * (4 * m + 1) ^ 4) * ((Cm * (xu ^ k)⁻¹) / ((z ^ 30)⁻¹) ^ (2 * k)) ≤
      (4 * 17 ^ 4 * 2 ^ k * Cm) * x ^ (-(N : ℝ)) := by
  have hx0 : 0 < x := by rw [hx]; positivity
  have hxu0 : 0 < xu := by linarith [(by positivity : 0 < x / 2)]
  have h1 : 4 * m + 1 ≤ 17 * z ^ 2 := by
    have : 1 ≤ z ^ 2 := by nlinarith
    linarith
  have h2 : (4 * m + 1) ^ 4 ≤ 17 ^ 4 * z ^ 8 := by
    calc (4 * m + 1) ^ 4 ≤ (17 * z ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
      _ = _ := by ring
  have h3 : (xu ^ k)⁻¹ ≤ 2 ^ k * (x ^ k)⁻¹ := by
    have a1 : (x / 2) ^ k ≤ xu ^ k := pow_le_pow_left₀ (by positivity) hxu k
    have a2 : (xu ^ k)⁻¹ ≤ ((x / 2) ^ k)⁻¹ := inv_anti₀ (by positivity) a1
    refine a2.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
  have h4 : (((z ^ 30)⁻¹) ^ (2 * k))⁻¹ = z ^ (60 * k) := by
    rw [inv_pow, inv_inv, ← pow_mul]
    congr 1
    ring
  have e5 : (Cm * (xu ^ k)⁻¹) / ((z ^ 30)⁻¹) ^ (2 * k) = Cm * (xu ^ k)⁻¹ * z ^ (60 * k) := by
    rw [div_eq_mul_inv, h4]
  rw [e5]
  have h6 : z ^ 8 * (z ^ (60 * k) * (x ^ k)⁻¹) ≤ x ^ (-(N : ℝ)) := by
    have a1 : x ^ k = z ^ (100 * k) := by
      rw [hx, ← pow_mul]
    have a2 : x ^ (-(N : ℝ)) = (z ^ (100 * N))⁻¹ := by
      rw [Real.rpow_neg hx0.le, Real.rpow_natCast, hx, ← pow_mul]
    rw [a1, a2]
    have a3 : z ^ 8 * (z ^ (60 * k) * (z ^ (100 * k))⁻¹) * z ^ (100 * N) ≤ 1 := by
      have b1 : z ^ 8 * z ^ (60 * k) * z ^ (100 * N) ≤ z ^ (100 * k) := by
        rw [← pow_add, ← pow_add]
        exact pow_le_pow_right₀ hz (by omega)
      have b2 : 0 < z ^ (100 * k) := by positivity
      calc z ^ 8 * (z ^ (60 * k) * (z ^ (100 * k))⁻¹) * z ^ (100 * N) =
          (z ^ 8 * z ^ (60 * k) * z ^ (100 * N)) * (z ^ (100 * k))⁻¹ := by ring
        _ ≤ z ^ (100 * k) * (z ^ (100 * k))⁻¹ := mul_le_mul_of_nonneg_right b1 (by positivity)
        _ = 1 := mul_inv_cancel₀ b2.ne'
    have b3 : 0 < z ^ (100 * N) := by positivity
    have a4 := (le_div_iff₀ b3).2 a3
    rwa [one_div] at a4
  calc (4 * (4 * m + 1) ^ 4) * (Cm * (xu ^ k)⁻¹ * z ^ (60 * k))
      ≤ (4 * (17 ^ 4 * z ^ 8)) * (Cm * (2 ^ k * (x ^ k)⁻¹) * z ^ (60 * k)) := by
        refine mul_le_mul (by linarith) ?_ (by positivity) (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 hC
    _ = (4 * 17 ^ 4 * 2 ^ k * Cm) * (z ^ 8 * (z ^ (60 * k) * (x ^ k)⁻¹)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h6 (by positivity)
end Numbers
section Forms
variable {m : ℕ}
private theorem imaginaryComponent_zero (e : Fin 3) : imaginaryComponent e (0 : imaginaryQuaternions) = 0 := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_toImaginary (e : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    imaginaryComponent e (ColdStepAtMirrorFrames.toImaginary v) = v e := by
  fin_cases e <;> rfl
private theorem freeCoordForm_eq_toColourForm {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) :
    freeCoordForm s η = toColourForm (freeImaginaryCoord s η) := by
  classical
  funext e b
  unfold freeCoordForm toColourForm freeImaginaryCoord
  split_ifs with h
  · exact (imaginaryComponent_toImaginary e _).symm
  · exact (imaginaryComponent_zero e).symm
private theorem curlNorm_indicator_le {X : Type} (E : Set X) (F : X → ColourForm m) (η : X) (p : TorusPlaquette m) :
    curlNorm (Set.indicator E F η) p ≤ curlNorm (F η) p := by
  classical
  by_cases h : η ∈ E
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    have : curlNorm (0 : ColourForm m) p = 0 := by
      simp [curlNorm, WeightedResponses.curl]
    rw [this]
    exact Real.sqrt_nonneg _
private theorem norm_lieFormCurl_le (A : TorusBond m → imaginaryQuaternions) (x : TorusSite m) (μ ν : Fin 4) :
    ‖lieFormCurl A (x, μ, ν)‖ ≤ plaquetteLogSize A x μ ν := by
  unfold lieFormCurl plaquetteLogSize
  refine (norm_sub_le _ _).trans ?_
  gcongr
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact norm_add_le _ _
private theorem plaquetteSum_eq (e : TorusBond m → ℝ) (x : TorusSite m) (μ ν : Fin 4) [NeZero m] :
    plaquetteSum e x μ ν = e (x, μ) + e (x + _root_.YangMills.Construction.TorusFields.unitStep m μ, ν) + e (x + _root_.YangMills.Construction.TorusFields.unitStep m ν, μ) + e (x, ν) := by
  simp [plaquetteSum, pathSum, plaquetteBonds]
  ring
end Forms
section Pointwise
variable {N : ℕ} [NeZero N]
private theorem cutoffProfile_eq_zero (o z : TorusSite N) (m : ℕ) (hm : 1 ≤ m) (h : 2 * m ≤ _root_.YangMills.Construction.TorusFields.supDist z o) : cutoffProfile o m z = 0 := by
  unfold cutoffProfile
  have h2 : (2 * (m : ℝ)) ≤ (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) := by exact_mod_cast h
  have h3 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h4 : (2 * (m : ℝ) - 1 - (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  exact max_eq_left ((min_le_right _ _).trans h4)
private theorem supDist_le_unitStep_add (x o : TorusSite N) (μ : Fin 4) : _root_.YangMills.Construction.TorusFields.supDist x o ≤ _root_.YangMills.Construction.TorusFields.supDist (x + _root_.YangMills.Construction.TorusFields.unitStep N μ) o + 1 := by
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle x (x + _root_.YangMills.Construction.TorusFields.unitStep N μ) o
  have h2 := supDist_add_unitStep_le x μ
  omega
private theorem supDist_unitStep_le (x o : TorusSite N) (μ : Fin 4) : _root_.YangMills.Construction.TorusFields.supDist (x + _root_.YangMills.Construction.TorusFields.unitStep N μ) o ≤ _root_.YangMills.Construction.TorusFields.supDist x o + 1 := by
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (x + _root_.YangMills.Construction.TorusFields.unitStep N μ) x o
  have h2 := supDist_add_unitStep_le x μ
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h2
  omega
private theorem lieFormCurl_cutoffCoords_far (ℓ : TorusLumps.StepParameters) (W : TorusField N) (o x : TorusSite N) (m : ℕ) (hm : 1 ≤ m)
    (μ ν : Fin 4) (hd : 2 * m + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist x o) :
    lieFormCurl (cutoffCoords ℓ W o m) (x, μ, ν) = 0 := by
  have h1 := supDist_le_unitStep_add x o μ
  have h2 := supDist_le_unitStep_add x o ν
  simp only [lieFormCurl, cutoffCoords]
  rw [cutoffProfile_eq_zero o x m hm (by omega), cutoffProfile_eq_zero o (x + _root_.YangMills.Construction.TorusFields.unitStep N μ) m hm (by omega),
    cutoffProfile_eq_zero o (x + _root_.YangMills.Construction.TorusFields.unitStep N ν) m hm (by omega)]
  simp
end Pointwise
section Moments
variable {N : ℕ} [NeZero N] {X : Type} [MeasurableSpace X]
private theorem moment_curl_difference (hP : cutoffCurlOverReferenceStatement) (hMl : momentBoundStatement)
    (ℓ : TorusLumps.StepParameters) (o : TorusSite N) (D : ℕ) (μ₀ : Measure X) [IsProbabilityMeasure μ₀] (Wf : X → TorusField N)
    (W₀ : TorusField N) (M : TorusBond N → imaginaryQuaternions)
    (Nf : X → TorusBond N → imaginaryQuaternions) (e : TorusBond N → X → ℝ) (hme : ∀ c, Measurable (e c)) (he0 : ∀ c x, 0 ≤ e c x)
    (v ω κ ε : ℝ)
    (hO : ∀ᵐ η ∂μ₀, IsNearReference o D (Wf η) W₀ M (Nf η) (fun c => e c η) v ω κ) (he1 : ∀ᵐ η ∂μ₀, ∀ c, e c η ≤ 1 / 64)
    (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hv1 : v ≤ 1) (hω : 0 ≤ ω) (hε : 0 < ε) (hN : 2 * D + 2 < N)
    (hsm : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1)
    (x : TorusSite N) (μ ν : Fin 4) (hμν : μ < ν) (hd : _root_.YangMills.Construction.TorusFields.supDist x o + 3 ≤ D) (q : ℕ) (hq : 1 ≤ q) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hm : ∀ c, eLpNorm (e c) ((2 * q : ℕ) : ENNReal) μ₀ ≤ ENNReal.ofReal b)
    (hm' : ∀ c, eLpNorm (e c) ((20 * q : ℕ) : ENNReal) μ₀ ≤ ENNReal.ofReal b') (g : X → ℝ)
    (hg : ∀ᵐ η ∂μ₀, |g η| ≤ ‖lieFormCurl (axialCoords ℓ (Wf η) o) (x, μ, ν) - lieFormCurl M (x, μ, ν) - lieFormCurl (Nf η) (x, μ, ν)‖) :
    eLpNorm g (q : ENNReal) μ₀ ≤ ENNReal.ofReal (2 * 10 ^ 5 * κ ^ 2 *
      (((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (((plaquetteBonds x μ ν).length : ℝ) * b) + ((plaquettePathBonds o x μ ν).length : ℝ) * b) ^ 2 +
      4 * ω + 0 * (((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (((plaquetteBonds x μ ν).length : ℝ) * b) + ((plaquettePathBonds o x μ ν).length : ℝ) * b) +
      0 * (((plaquetteBonds x μ ν).length : ℝ) * b) + 20 * (((plaquettePathBonds o x μ ν).length : ℝ) * (b' / ε) ^ 20)) := by
  refine hMl.1 X μ₀ (TorusBond N) e hme he0 (plaquetteBonds x μ ν) (plaquettePathBonds o x μ ν) q b b' ε _ ((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) 0 0 (4 * ω)
    (2 * 10 ^ 5 * κ ^ 2) hq hb hb' hε (by positivity) (by positivity) le_rfl le_rfl (by positivity) (by positivity) hm hm' g ?_
  filter_upwards [hO, he1, hg] with η h1 h2 h3
  refine h3.trans ?_
  have pc := hP.1 ℓ N o D (Wf η) W₀ M (Nf η) (fun c => e c η) v ω κ ε h1 hκ hv hv1 hω hε hN hsm h2 x μ ν hμν hd
  refine pc.trans (le_of_eq ?_)
  have s1 : plaquetteSum (fun c => e c η) x μ ν = sumAlong e (plaquetteBonds x μ ν) η := rfl
  have s2 : pathSum (fun c => e c η) (plaquettePathBonds o x μ ν) = sumAlong e (plaquettePathBonds o x μ ν) η := rfl
  have s3 : pathSum (fun c => (e c η / ε) ^ 20) (plaquettePathBonds o x μ ν) =
      sumAlong (fun c x => (e c x / ε) ^ 20) (plaquettePathBonds o x μ ν) η := rfl
  rw [s1, s2, s3]
  ring
private theorem moment_curl_cutoff (hP : cutoffCurlOverReferenceStatement) (hMl : momentBoundStatement)
    (ℓ : TorusLumps.StepParameters) (o : TorusSite N) (D m : ℕ) (μ₀ : Measure X) [IsProbabilityMeasure μ₀] (Wf : X → TorusField N)
    (W₀ : TorusField N) (M : TorusBond N → imaginaryQuaternions)
    (Nf : X → TorusBond N → imaginaryQuaternions) (e : TorusBond N → X → ℝ) (hme : ∀ c, Measurable (e c)) (he0 : ∀ c x, 0 ≤ e c x)
    (v ω κ ε : ℝ)
    (hO : ∀ᵐ η ∂μ₀, IsNearReference o D (Wf η) W₀ M (Nf η) (fun c => e c η) v ω κ)
    (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hε : 0 < ε) (hN : 2 * D + 2 < N) (hm2 : 2 ≤ m)
    (hsm : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1)
    (x : TorusSite N) (μ ν : Fin 4) (hμν : μ < ν) (hd : _root_.YangMills.Construction.TorusFields.supDist x o + 3 ≤ D) (q : ℕ) (hq : 1 ≤ q) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hm : ∀ c, eLpNorm (e c) ((2 * q : ℕ) : ENNReal) μ₀ ≤ ENNReal.ofReal b)
    (hm' : ∀ c, eLpNorm (e c) ((20 * q : ℕ) : ENNReal) μ₀ ≤ ENNReal.ofReal b') (g : X → ℝ)
    (hg : ∀ᵐ η ∂μ₀, |g η| ≤ ‖lieFormCurl (cutoffCoords ℓ (Wf η) o m) (x, μ, ν)‖) :
    eLpNorm g (q : ENNReal) μ₀ ≤ ENNReal.ofReal (2 * 10 ^ 5 * κ ^ 2 *
      (((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (((plaquetteBonds x μ ν).length : ℝ) * b) + ((plaquettePathBonds o x μ ν).length : ℝ) * b) ^ 2 +
      (4 * ω + v / 16) + 124 / ((m : ℝ) - 1) * (((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2) * (((plaquetteBonds x μ ν).length : ℝ) * b) + ((plaquettePathBonds o x μ ν).length : ℝ) * b) +
      1 * (((plaquetteBonds x μ ν).length : ℝ) * b) + 20 * (((plaquettePathBonds o x μ ν).length : ℝ) * (b' / ε) ^ 20)) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  refine hMl.1 X μ₀ (TorusBond N) e hme he0 (plaquetteBonds x μ ν) (plaquettePathBonds o x μ ν) q b b' ε _ ((_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 2)
    (124 / ((m : ℝ) - 1)) 1
    (4 * ω + v / 16) (2 * 10 ^ 5 * κ ^ 2) hq hb hb' hε (by positivity) (by positivity) (by positivity) zero_le_one (by positivity)
    (by positivity) hm hm' g ?_
  filter_upwards [hO, hg] with η h1 h3
  refine h3.trans ?_
  have pc := hP.2.1 ℓ N o D m (Wf η) W₀ M (Nf η) (fun c => e c η) v ω κ ε h1 hκ hv hω hε hN hm2 hsm x μ ν hμν hd
  refine pc.trans (le_of_eq ?_)
  have s1 : plaquetteSum (fun c => e c η) x μ ν = sumAlong e (plaquetteBonds x μ ν) η := rfl
  have s2 : pathSum (fun c => e c η) (plaquettePathBonds o x μ ν) = sumAlong e (plaquettePathBonds o x μ ν) η := rfl
  have s3 : pathSum (fun c => (e c η / ε) ^ 20) (plaquettePathBonds o x μ ν) =
      sumAlong (fun c x => (e c x / ε) ^ 20) (plaquettePathBonds o x μ ν) η := rfl
  rw [s1, s2, s3]
  ring
private theorem moment_curl_free (hMl : momentBoundStatement) (o : TorusSite N) (D : ℕ) (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (Wf : X → TorusField N) (W₀ : TorusField N) (M : TorusBond N → imaginaryQuaternions) (Nf : X → TorusBond N → imaginaryQuaternions)
    (e : TorusBond N → X → ℝ) (hme : ∀ c, Measurable (e c))
    (he0 : ∀ c x, 0 ≤ e c x) (v ω κ : ℝ) (hO : ∀ᵐ η ∂μ₀, IsNearReference o D (Wf η) W₀ M (Nf η) (fun c => e c η) v ω κ)
    (hv : 0 ≤ v) (x : TorusSite N) (μ ν : Fin 4) (hμν : μ < ν) (q : ℕ) (hq : 1 ≤ q) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hm : ∀ c, eLpNorm (e c) ((2 * q : ℕ) : ENNReal) μ₀ ≤ ENNReal.ofReal b)
    (hm' : ∀ c, eLpNorm (e c) ((20 * q : ℕ) : ENNReal) μ₀ ≤ ENNReal.ofReal b') (g : X → ℝ)
    (hg : ∀ᵐ η ∂μ₀, |g η| ≤ ‖lieFormCurl (fun c => M c + Nf η c) (x, μ, ν)‖) :
    eLpNorm g (q : ENNReal) μ₀ ≤ ENNReal.ofReal (v / 16 + 4 * b) := by
  have key := hMl.1 X μ₀ (TorusBond N) e hme he0 (plaquetteBonds x μ ν) [] q b b' 1 0 0 0 1 (v / 16) 0 hq hb hb' one_pos le_rfl le_rfl
    le_rfl zero_le_one (by positivity) le_rfl hm hm' g ?_
  · refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp [plaquetteBonds]
  · filter_upwards [hO, hg] with η h1 h3
    refine h3.trans ?_
    have e1 : lieFormCurl (fun c => M c + Nf η c) (x, μ, ν) = lieFormCurl M (x, μ, ν) + lieFormCurl (Nf η) (x, μ, ν) := by
      simp only [lieFormCurl]
      module
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have c1 := h1.curl_le x μ ν hμν
    have c2 : ‖lieFormCurl (Nf η) (x, μ, ν)‖ ≤ sumAlong e (plaquetteBonds x μ ν) η := by
      refine (norm_lieFormCurl_le (Nf η) x μ ν).trans ?_
      have s1 : sumAlong e (plaquetteBonds x μ ν) η = plaquetteSum (fun c => e c η) x μ ν := rfl
      rw [s1, plaquetteSum_eq]
      unfold plaquetteLogSize
      have a1 := h1.free_le (x, μ)
      have a2 := h1.free_le (x + _root_.YangMills.Construction.TorusFields.unitStep N μ, ν)
      have a3 := h1.free_le (x + _root_.YangMills.Construction.TorusFields.unitStep N ν, μ)
      have a4 := h1.free_le (x, ν)
      linarith
    have z1 : sumAlong e ([] : List (TorusBond N)) η = 0 := by simp [sumAlong]
    have z2 : sumAlong (fun c x => (e c x / 1) ^ 20) ([] : List (TorusBond N)) η = 0 := by simp [sumAlong]
    rw [z1, z2]
    linarith
end Moments
section Law
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by
  have h2 := Quaternion.normSq_eq_norm_mul_self ((ColdStepAtMirrorFrames.toImaginary v : imaginaryQuaternions) : ℍ[ℝ])
  have h3 : Quaternion.normSq ((ColdStepAtMirrorFrames.toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) = ‖v‖ ^ 2 := by
    rw [Quaternion.normSq_def', EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    show (0 : ℝ) ^ 2 + v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = _
    ring
  have h4 : ‖((ColdStepAtMirrorFrames.toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← h3, h2]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h4
private theorem freeCoordSize_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) (c : TorusBond (n * R.params.side)) :
    0 ≤ freeCoordSize s η c := by
  classical
  unfold freeCoordSize
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl
private theorem measurable_freeCoordSize (s : ChartSetting R n) (c : TorusBond (n * R.params.side)) :
    Measurable fun η : FreeCoords s.free => freeCoordSize s η c := by
  classical
  unfold freeCoordSize
  by_cases h : c ∈ s.free
  · simp only [dif_pos h, coordNorm_eq_norm]
    exact measurable_norm.comp (measurable_pi_apply _)
  · simp only [dif_neg h]
    exact measurable_const
private structure ColdLawData (R : StepSetup) {n : ℕ} [NeZero n] (A : TorusBond n → imaginaryQuaternions)
    (M : TorusBond (n * R.params.side) → imaginaryQuaternions)
    (o : TorusSite (n * R.params.side)) (D : ℕ) (v ω κ ε : ℝ) : Prop where
  near : ∀ η : FreeCoords (coldSettingOver R (expField 1 A)).free, (∀ b, coordNorm (η b) ≤ R.ballRadius) →
    IsNearReference o D ((coldSettingOver R (expField 1 A)).field η) ((coldSettingOver R (expField 1 A)).field 0) M
      (freeImaginaryCoord (coldSettingOver R (expField 1 A)) η) (freeCoordSize (coldSettingOver R (expField 1 A)) η) v ω κ
  isProb : IsProbabilityMeasure (coldFreeLaw R (expField 1 A))
  ball_lt : ∀ᵐ η ∂(coldFreeLaw R (expField 1 A)), ∀ b, coordNorm (η b) < R.ballRadius
  radius_le : R.ballRadius ≤ 1 / 64
  one_le : 1 ≤ κ
  v_nonneg : 0 ≤ v
  v_le : v ≤ 1
  ω_nonneg : 0 ≤ ω
  ε_pos : 0 < ε
  lt_side : 2 * D + 2 < n * R.params.side
  small_le : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1
private theorem freeCoordSize_le (s : ChartSetting R n) (hρ : R.ballRadius ≤ 1 / 64) (η : FreeCoords s.free)
    (hη : ∀ b, coordNorm (η b) < R.ballRadius)
    (hρ0 : 0 ≤ R.ballRadius) (c : TorusBond (n * R.params.side)) : freeCoordSize s η c ≤ 1 / 64 := by
  classical
  unfold freeCoordSize
  split_ifs with h
  · exact (hη _).le.trans hρ
  · norm_num
private theorem measure_boxCurvature_gt_le (hP : cutoffCurlOverReferenceStatement) (ℓ : TorusLumps.StepParameters)
    {A : TorusBond n → imaginaryQuaternions} {M : TorusBond (n * R.params.side) → imaginaryQuaternions}
    {o : TorusSite (n * R.params.side)} {D : ℕ} {v ω κ ε : ℝ} (hL : ColdLawData R A M o D v ω κ ε) (m : ℕ) (Xb : ℝ)
    (hXb : v / 2 + 8 * ε + 5 * ω ≤ Xb) (hD : 2 * m + 1 ≤ D) :
    (coldFreeLaw R (expField 1 A)) {η | ¬ boxCurvature o (2 * m) ((coldSettingOver R (expField 1 A)).field η) ≤ Xb} ≤
      ∑ c ∈ (TorusLumps.thickening (2 * m) {o}) ×ˢ (Finset.univ : Finset (Fin 4)),
        (coldFreeLaw R (expField 1 A)) {η | ε ≤ freeCoordSize (coldSettingOver R (expField 1 A)) η c} := by
  classical
  have hv := hL.v_nonneg
  have hω := hL.ω_nonneg
  have hε := hL.ε_pos
  have hX0 : 0 ≤ Xb := by
    refine le_trans ?_ hXb
    positivity
  have hsub : {η : FreeCoords (coldSettingOver R (expField 1 A)).free |
        ¬ boxCurvature o (2 * m) ((coldSettingOver R (expField 1 A)).field η) ≤ Xb} ⊆
      {η | ¬ ∀ b, coordNorm (η b) < R.ballRadius} ∪
        ⋃ c ∈ (TorusLumps.thickening (2 * m) {o}) ×ˢ (Finset.univ : Finset (Fin 4)),
          {η | ε ≤ freeCoordSize (coldSettingOver R (expField 1 A)) η c} := by
    intro η hη
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists, not_le] at hcon
    obtain ⟨hb, hsm⟩ := hcon
    apply hη
    have hO := hL.near η (fun b => (hb b).le)
    have hnear : ∀ c : TorusBond (n * R.params.side), _root_.YangMills.Construction.TorusFields.supDist c.1 o ≤ 2 * m →
        freeCoordSize (coldSettingOver R (expField 1 A)) η c < ε := by
      intro c hc
      refine hsm c ?_
      refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, o, Finset.mem_singleton_self o, hc⟩
    exact hP.2.2 ℓ _ o D m _ _ M _ _ v ω κ ε Xb hO hL.one_le hv hω hε.le hL.lt_side hL.small_le hD hXb hX0 hnear
  have hzero : (coldFreeLaw R (expField 1 A)) {η | ¬ ∀ b, coordNorm (η b) < R.ballRadius} = 0 := hL.ball_lt
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hzero, zero_add]
  exact measure_biUnion_finset_le _ _
private theorem toColourForm_sub (hCo : colourFormIdentitiesStatement) {m : ℕ} (a M Nf : TorusBond m → imaginaryQuaternions) :
    (fun e b => toColourForm a e b - (fun e b => toColourForm M e b + toColourForm Nf e b) e b) =
      toColourForm fun b => a b - (M b + Nf b) := by
  have h1 := hCo.2.2.1 m M Nf
  have h2 := hCo.2.2.2 m a fun b => M b + Nf b
  rw [← h2, ← h1]
private theorem curlNorm_sub (hCo : colourFormIdentitiesStatement) {m : ℕ} (a M Nf : TorusBond m → imaginaryQuaternions)
    (p : TorusPlaquette m) :
    curlNorm (fun e b => toColourForm a e b - (fun e b => toColourForm M e b + toColourForm Nf e b) e b) p =
      ‖lieFormCurl a p - lieFormCurl M p - lieFormCurl Nf p‖ := by
  rw [toColourForm_sub hCo, hCo.1]
  congr 1
  simp only [lieFormCurl]
  module
private theorem curlNorm_add (hCo : colourFormIdentitiesStatement) {m : ℕ} (M Nf : TorusBond m → imaginaryQuaternions)
    (p : TorusPlaquette m) :
    curlNorm (fun e b => toColourForm M e b + toColourForm Nf e b) p = ‖lieFormCurl (fun c => M c + Nf c) p‖ := by
  rw [hCo.2.2.1 m M Nf, hCo.1]
private theorem curlNorm_nonneg {m : ℕ} (Z : ColourForm m) (p : TorusPlaquette m) : 0 ≤ curlNorm Z p := Real.sqrt_nonneg _
private theorem curl_moment_near (hP : cutoffCurlOverReferenceStatement) (hMl : momentBoundStatement)
    (hCo : colourFormIdentitiesStatement) {A : TorusBond n → imaginaryQuaternions}
    {M : TorusBond (n * R.params.side) → imaginaryQuaternions}
    {o : TorusSite (n * R.params.side)} {D : ℕ} {v ω κ ε : ℝ} (hL : ColdLawData R A M o D v ω κ ε) (hρ0 : 0 ≤ R.ballRadius)
    (Xc : ColourForm (n * R.params.side)) (hXc : Xc = toColourForm M)
    (E : Set (FreeCoords (coldSettingOver R (expField 1 A)).free)) (p : WeightedResponses.OrientedPlaquette (n * R.params.side))
    (hd : _root_.YangMills.Construction.TorusFields.supDist p.1.1 o + 3 ≤ D)
    (q : ℕ) (hq : 1 ≤ q) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hm : ∀ c : TorusBond (n * R.params.side), eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c)
      ((2 * q : ℕ) : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal b)
    (hm' : ∀ c : TorusBond (n * R.params.side), eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c)
      ((20 * q : ℕ) : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal b') :
    eLpNorm (Set.indicator E (fun η => curlNorm (fun e c => toColourForm (axialCoords R.params ((coldSettingOver R (expField 1 A)).field η) o) e c -
        (fun e c => Xc e c + freeCoordForm (coldSettingOver R (expField 1 A)) η e c) e c) p.1)) (q : ENNReal) (coldFreeLaw R (expField 1 A)) ≤
      ENNReal.ofReal (2 * 10 ^ 5 * κ ^ 2 *
      (((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) + ((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) ^ 2 +
      4 * ω + 0 * (((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) + ((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) +
      0 * (((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) + 20 * (((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * (b' / ε) ^ 20)) := by
  haveI := hL.isProb
  obtain ⟨⟨x, μ, ν⟩, hμν⟩ := p
  refine moment_curl_difference hP hMl R.params o D (coldFreeLaw R (expField 1 A)) (fun η => (coldSettingOver R (expField 1 A)).field η)
    ((coldSettingOver R (expField 1 A)).field 0) M (fun η => freeImaginaryCoord (coldSettingOver R (expField 1 A)) η)
    (fun c η => freeCoordSize (coldSettingOver R (expField 1 A)) η c) (fun c => measurable_freeCoordSize _ c)
    (fun c η => freeCoordSize_nonneg _ η c) v ω κ ε ?_ ?_
    hL.one_le hL.v_nonneg hL.v_le hL.ω_nonneg hL.ε_pos hL.lt_side hL.small_le x μ ν hμν hd q hq b b' hb hb' hm hm' _ ?_
  · filter_upwards [hL.ball_lt] with η h
    exact hL.near η fun b => (h b).le
  · filter_upwards [hL.ball_lt] with η h c
    exact freeCoordSize_le _ hL.radius_le η h hρ0 c
  · filter_upwards with η
    classical
    have hsz : curlNorm (fun e c => toColourForm (axialCoords R.params ((coldSettingOver R (expField 1 A)).field η) o) e c -
        (fun e c => Xc e c + freeCoordForm (coldSettingOver R (expField 1 A)) η e c) e c) (x, μ, ν) =
        ‖lieFormCurl (axialCoords R.params ((coldSettingOver R (expField 1 A)).field η) o) (x, μ, ν) - lieFormCurl M (x, μ, ν) -
          lieFormCurl (freeImaginaryCoord (coldSettingOver R (expField 1 A)) η) (x, μ, ν)‖ := by
      rw [hXc, freeCoordForm_eq_toColourForm]
      exact curlNorm_sub hCo _ _ _ _
    by_cases h : η ∈ E
    · rw [Set.indicator_of_mem h, abs_of_nonneg (curlNorm_nonneg _ _)]
      exact le_of_eq hsz
    · rw [Set.indicator_of_notMem h, abs_zero]
      exact norm_nonneg _
private theorem cutoff_moment_near (hP : cutoffCurlOverReferenceStatement) (hMl : momentBoundStatement)
    (hCo : colourFormIdentitiesStatement) {A : TorusBond n → imaginaryQuaternions}
    {M : TorusBond (n * R.params.side) → imaginaryQuaternions}
    {o : TorusSite (n * R.params.side)} {D : ℕ} {v ω κ ε : ℝ} (hL : ColdLawData R A M o D v ω κ ε) (m : ℕ) (hm2 : 2 ≤ m)
    (E : Set (FreeCoords (coldSettingOver R (expField 1 A)).free)) (p : WeightedResponses.OrientedPlaquette (n * R.params.side))
    (hd : _root_.YangMills.Construction.TorusFields.supDist p.1.1 o + 3 ≤ D)
    (q : ℕ) (hq : 1 ≤ q) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hm : ∀ c : TorusBond (n * R.params.side), eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c)
      ((2 * q : ℕ) : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal b)
    (hm' : ∀ c : TorusBond (n * R.params.side), eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c)
      ((20 * q : ℕ) : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal b') :
    eLpNorm (fun η => curlNorm (Set.indicator E (fun η => toColourForm (cutoffCoords R.params ((coldSettingOver R (expField 1 A)).field η) o m)) η) p.1)
      (q : ENNReal) (coldFreeLaw R (expField 1 A)) ≤
      ENNReal.ofReal (2 * 10 ^ 5 * κ ^ 2 *
      (((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) + ((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) ^ 2 +
      (4 * ω + v / 16) + 124 / ((m : ℝ) - 1) * (((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (v + ω) + ((_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) + 2) * (((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) + ((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) +
      1 * (((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * b) + 20 * (((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ) * (b' / ε) ^ 20)) := by
  haveI := hL.isProb
  obtain ⟨⟨x, μ, ν⟩, hμν⟩ := p
  refine moment_curl_cutoff hP hMl R.params o D m (coldFreeLaw R (expField 1 A)) (fun η => (coldSettingOver R (expField 1 A)).field η)
    ((coldSettingOver R (expField 1 A)).field 0) M (fun η => freeImaginaryCoord (coldSettingOver R (expField 1 A)) η)
    (fun c η => freeCoordSize (coldSettingOver R (expField 1 A)) η c) (fun c => measurable_freeCoordSize _ c)
    (fun c η => freeCoordSize_nonneg _ η c) v ω κ ε ?_
    hL.one_le hL.v_nonneg hL.ω_nonneg hL.ε_pos hL.lt_side hm2 hL.small_le x μ ν hμν hd q hq b b' hb hb' hm hm' _ ?_
  · filter_upwards [hL.ball_lt] with η h
    exact hL.near η fun b => (h b).le
  · filter_upwards with η
    rw [abs_of_nonneg (curlNorm_nonneg _ _)]
    refine (curlNorm_indicator_le E _ η _).trans (le_of_eq ?_)
    exact hCo.1 _ _ _
private theorem cutoff_moment_far (hCo : colourFormIdentitiesStatement) {A : TorusBond n → imaginaryQuaternions}
    {o : TorusSite (n * R.params.side)} (m : ℕ) (hm : 1 ≤ m)
    (E : Set (FreeCoords (coldSettingOver R (expField 1 A)).free)) (p : WeightedResponses.OrientedPlaquette (n * R.params.side))
    (hd : 2 * m + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist p.1.1 o)
    (q : ENNReal) :
    eLpNorm (fun η => curlNorm (Set.indicator E (fun η => toColourForm (cutoffCoords R.params ((coldSettingOver R (expField 1 A)).field η) o m)) η) p.1)
      q (coldFreeLaw R (expField 1 A)) = 0 := by
  obtain ⟨⟨x, μ, ν⟩, hμν⟩ := p
  have : (fun η => curlNorm (Set.indicator E (fun η => toColourForm (cutoffCoords R.params ((coldSettingOver R (expField 1 A)).field η) o m)) η) (x, μ, ν)) =
      fun _ => (0 : ℝ) := by
    funext η
    refine le_antisymm ((curlNorm_indicator_le E _ η _).trans (le_of_eq ?_)) (curlNorm_nonneg _ _)
    rw [hCo.1, lieFormCurl_cutoffCoords_far R.params _ o x m hm μ ν hd, norm_zero]
  show eLpNorm (fun η => curlNorm (Set.indicator E (fun η => toColourForm (cutoffCoords R.params ((coldSettingOver R (expField 1 A)).field η) o m)) η) (x, μ, ν)) q _ = 0
  rw [this, eLpNorm_zero']
private theorem free_moment (hMl : momentBoundStatement) (hCo : colourFormIdentitiesStatement) {A : TorusBond n → imaginaryQuaternions}
    {M : TorusBond (n * R.params.side) → imaginaryQuaternions}
    {o : TorusSite (n * R.params.side)} {D : ℕ} {v ω κ ε : ℝ} (hL : ColdLawData R A M o D v ω κ ε) (Xc : ColourForm (n * R.params.side))
    (hXc : Xc = toColourForm M)
    (E : Set (FreeCoords (coldSettingOver R (expField 1 A)).free)) (p : WeightedResponses.OrientedPlaquette (n * R.params.side))
    (q : ℕ) (hq : 1 ≤ q) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hm : ∀ c : TorusBond (n * R.params.side), eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c)
      ((2 * q : ℕ) : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal b)
    (hm' : ∀ c : TorusBond (n * R.params.side), eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c)
      ((20 * q : ℕ) : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal b') :
    eLpNorm (fun η => curlNorm (Set.indicator E (fun η => fun e c => Xc e c + freeCoordForm (coldSettingOver R (expField 1 A)) η e c) η) p.1)
      (q : ENNReal) (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal (v / 16 + 4 * b) := by
  haveI := hL.isProb
  obtain ⟨⟨x, μ, ν⟩, hμν⟩ := p
  refine moment_curl_free hMl o D (coldFreeLaw R (expField 1 A)) (fun η => (coldSettingOver R (expField 1 A)).field η)
    ((coldSettingOver R (expField 1 A)).field 0) M (fun η => freeImaginaryCoord (coldSettingOver R (expField 1 A)) η)
    (fun c η => freeCoordSize (coldSettingOver R (expField 1 A)) η c) (fun c => measurable_freeCoordSize _ c)
    (fun c η => freeCoordSize_nonneg _ η c) v ω κ ?_
    hL.v_nonneg x μ ν hμν q hq b b' hb hb' hm hm' _ ?_
  · filter_upwards [hL.ball_lt] with η h
    exact hL.near η fun b => (h b).le
  · filter_upwards with η
    rw [abs_of_nonneg (curlNorm_nonneg _ _)]
    refine (curlNorm_indicator_le E _ η _).trans (le_of_eq ?_)
    rw [hXc, freeCoordForm_eq_toColourForm]
    exact curlNorm_add hCo _ _ _
private theorem plaquettePathBonds_length_le (hA : axialGaugePathBoundsStatement) (ℓ : TorusLumps.StepParameters) {N : ℕ} [NeZero N]
    (o x : TorusSite N) (μ ν : Fin 4) :
    ((plaquettePathBonds o x μ ν).length : ℝ) ≤ 16 * (_root_.YangMills.Construction.TorusFields.supDist x o : ℝ) + 20 := by
  have l₀ := (hA.1 ℓ N o x).2.2.2
  have l₁ := (hA.1 ℓ N o (x + _root_.YangMills.Construction.TorusFields.unitStep N μ)).2.2.2
  have l₂ := (hA.1 ℓ N o (x + _root_.YangMills.Construction.TorusFields.unitStep N ν)).2.2.2
  have l₃ := (hA.1 ℓ N o (x + _root_.YangMills.Construction.TorusFields.unitStep N μ + _root_.YangMills.Construction.TorusFields.unitStep N ν)).2.2.2
  have z₁ := supDist_unitStep_le x o μ
  have z₂ := supDist_unitStep_le x o ν
  have z₃ := supDist_unitStep_le (x + _root_.YangMills.Construction.TorusFields.unitStep N μ) o ν
  have : (plaquettePathBonds o x μ ν).length ≤ 16 * _root_.YangMills.Construction.TorusFields.supDist x o + 20 := by
    simp only [plaquettePathBonds, plaquetteBonds, List.length_append, List.length_cons, List.length_nil]
    omega
  have h2 : ((plaquettePathBonds o x μ ν).length : ℝ) ≤ ((16 * _root_.YangMills.Construction.TorusFields.supDist x o + 20 : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h2
  exact h2
private theorem free_constant_aux {c B w : ℝ} (hw : 0 ≤ w) (hB : 0 ≤ B) (hc : 1 + 4 * B ≤ c) : w / 16 + 4 * B * 1 ≤ c * (1 + w) := by
  have h1 : (1 + 4 * B) * (1 + w) ≤ c * (1 + w) := mul_le_mul_of_nonneg_right hc (by linarith)
  have h2 : 0 ≤ B * w := mul_nonneg hB hw
  nlinarith
private def momentConstant (K : ℝ) (B T : ℕ → ℝ) (q : ℕ) : ℝ :=
  K * (2 + 28 * B q) ^ 2 + 620 * (2 + 28 * B q) + 5 + 4 + 4 * B q + 400 * T q + 1 + 4 * B q
private theorem weightedCurvatureNorm_le {N : ℕ} [NeZero N] {Y : Type} [MeasurableSpace Y] (μ₀ : Measure Y) (ωf : TorusPlaquette N → ℝ)
    (hω1 : ∀ p, ωf p ≤ 1) (q : ENNReal) (Xf : Y → ColourForm N) (Tb xh : ℝ) (hxh : 0 ≤ xh) (hT : 0 ≤ Tb)
    (h : ∀ p : WeightedResponses.OrientedPlaquette N, eLpNorm (fun η => curlNorm (Xf η) p.1) q μ₀ ≤ ENNReal.ofReal Tb) :
    ENNReal.ofReal xh * weightedCurvatureNorm μ₀ ωf q Xf ≤ ENNReal.ofReal (xh * Tb) := by
  rw [ENNReal.ofReal_mul hxh]
  refine mul_le_mul_right ?_ _
  unfold weightedCurvatureNorm
  refine iSup_le fun p => ?_
  have h1 : ENNReal.ofReal (ωf p.1) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hω1 _)
  calc ENNReal.ofReal (ωf p.1) * eLpNorm (fun η => curlNorm (Xf η) p.1) q μ₀ ≤ 1 * ENNReal.ofReal Tb :=
        mul_le_mul' h1 (h p)
    _ = _ := one_mul _
private theorem moment_conditions (hP : cutoffCurlOverReferenceStatement) (hA : axialGaugePathBoundsStatement) (hMl : momentBoundStatement)
    (hCo : colourFormIdentitiesStatement) {A : TorusBond n → imaginaryQuaternions}
    {M : TorusBond (n * R.params.side) → imaginaryQuaternions}
    {o : TorusSite (n * R.params.side)} {D : ℕ} {v ω κ ε : ℝ} (hL : ColdLawData R A M o D v ω κ ε) (hρ0 : 0 ≤ R.ballRadius) (m : ℕ)
    (hm2 : 2 ≤ m)
    (hD : D = 2 * m + 6) (Xc : ColourForm (n * R.params.side)) (hXc : Xc = toColourForm M) (y xh : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hxh : 0 ≤ xh) (hxy : xh * y = 1)
    (hωy : ω ≤ y ^ 2) (hsq : (1 + 2 * (m : ℝ)) ^ 2 * (v + y) ≤ 1) (B T : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q) (hT : ∀ q, 0 ≤ T q)
    (hmom : ∀ q : ℕ, 1 ≤ q → ∀ c : TorusBond (n * R.params.side),
      eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c) ((2 * q : ℕ) : ENNReal)
      (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal (B q * y))
    (ht : ∀ q, (B (10 * q) * y / ε) ^ 20 ≤ T q * y ^ 2) (E : Set (FreeCoords (coldSettingOver R (expField 1 A)).free))
    (ωf : TorusPlaquette (n * R.params.side) → ℝ) (hω1 : ∀ p, ωf p ≤ 1) :
    (∀ (p : WeightedResponses.OrientedPlaquette (n * R.params.side)) (q : ℕ), 1 ≤ q → (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) ≤ 2 * m →
      eLpNorm (Set.indicator E (fun η => curlNorm (fun e c => toColourForm (axialCoords R.params ((coldSettingOver R (expField 1 A)).field η) o) e c -
        (fun e c => Xc e c + freeCoordForm (coldSettingOver R (expField 1 A)) η e c) e c) p.1)) (q : ENNReal) (coldFreeLaw R (expField 1 A)) ≤
      ENNReal.ofReal (momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q * (1 + (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ)) ^ 2 * (v + y) ^ 2)) ∧
    ∀ q : ℕ, 1 ≤ q →
      ENNReal.ofReal xh * weightedCurvatureNorm (coldFreeLaw R (expField 1 A)) ωf (q : ENNReal)
        (Set.indicator E fun η => toColourForm (cutoffCoords R.params ((coldSettingOver R (expField 1 A)).field η) o m)) ≤
        ENNReal.ofReal (momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q * (1 + xh * v)) ∧
      ENNReal.ofReal xh * weightedCurvatureNorm (coldFreeLaw R (expField 1 A)) ωf (q : ENNReal)
        (Set.indicator E fun η => fun e c => Xc e c + freeCoordForm (coldSettingOver R (expField 1 A)) η e c) ≤
        ENNReal.ofReal (momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q * (1 + xh * v)) := by
  have hv := hL.v_nonneg
  have hω := hL.ω_nonneg
  have hK : 0 ≤ 2 * 10 ^ 5 * κ ^ 2 := by positivity
  have hm'of : ∀ q : ℕ, 1 ≤ q → ∀ c : TorusBond (n * R.params.side),
      eLpNorm (fun η => freeCoordSize (coldSettingOver R (expField 1 A)) η c) ((20 * q : ℕ) : ENNReal)
      (coldFreeLaw R (expField 1 A)) ≤ ENNReal.ofReal (B (10 * q) * y) := by
    intro q hq c
    have := hmom (10 * q) (by omega) c
    rw [show 2 * (10 * q) = 20 * q by ring] at this
    exact this
  have hcf : ∀ q, 0 ≤ momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q := fun q => by
    have a := hB q
    have b := hT q
    unfold momentConstant
    positivity
  refine ⟨fun p q hq hd => ?_, fun q hq => ⟨?_, ?_⟩⟩
  · have hd' : _root_.YangMills.Construction.TorusFields.supDist p.1.1 o + 3 ≤ D := by
      have : _root_.YangMills.Construction.TorusFields.supDist p.1.1 o ≤ 2 * m := by exact_mod_cast hd
      omega
    refine (curl_moment_near hP hMl hCo hL hρ0 Xc hXc E p hd' q hq (B q * y) (B (10 * q) * y) (mul_nonneg (hB q) hy)
      (mul_nonneg (hB _) hy) (hmom q hq) (hm'of q hq)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hn := bound_curl_aux (K := 2 * 10 ^ 5 * κ ^ 2) (d := (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ)) (v := v) (y := y) (ω := ω) (b := B q * y) (B := B q)
      (Pl := ((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ)) (l := ((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ))
      (t := (B (10 * q) * y / ε) ^ 20) (T := T q) hK (by positivity) hv hy hy1 hω hωy (hB q) rfl (by positivity)
      (plaquettePathBonds_length_le hA R.params o _ _ _) (by simp [plaquetteBonds]) (ht q) (hT q)
    refine hn.trans ?_
    have hw : 0 ≤ (1 + (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ)) ^ 2 * (v + y) ^ 2 := by positivity
    have h2 : 2 * 10 ^ 5 * κ ^ 2 * (2 + 28 * B q) ^ 2 + 4 + 400 * T q ≤ momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q := by
      unfold momentConstant
      have a := hB q
      linarith
    have := mul_le_mul_of_nonneg_right h2 hw
    calc _ = (2 * 10 ^ 5 * κ ^ 2 * (2 + 28 * B q) ^ 2 + 4 + 400 * T q) * ((1 + (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ)) ^ 2 * (v + y) ^ 2) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · have hcfq := hcf q
    have hvy : 0 ≤ v + y := by positivity
    refine (weightedCurvatureNorm_le _ ωf hω1 _ _ (momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q * (v + y)) xh hxh (by positivity)
      fun p => ?_).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    · by_cases hfar : 2 * m + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist p.1.1 o
      · rw [cutoff_moment_far hCo m (by omega) E p hfar]
        exact zero_le
      · have hd0 : _root_.YangMills.Construction.TorusFields.supDist p.1.1 o ≤ 2 * m := by omega
        have hd1 : (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) ≤ 2 * m := by exact_mod_cast hd0
        have hd' : _root_.YangMills.Construction.TorusFields.supDist p.1.1 o + 3 ≤ D := by omega
        refine (cutoff_moment_near hP hMl hCo hL m hm2 E p hd' q hq (B q * y) (B (10 * q) * y) (mul_nonneg (hB q) hy)
          (mul_nonneg (hB _) hy) (hmom q hq) (hm'of q hq)).trans (ENNReal.ofReal_le_ofReal ?_)
        have hm2' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
        have hdn : (0 : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ) := by positivity
        have hs2 : (1 + (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ)) ^ 2 * (v + y) ≤ 1 := by
          refine le_trans (mul_le_mul_of_nonneg_right ?_ hvy) hsq
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
        have hn := bound_cut_aux (K := 2 * 10 ^ 5 * κ ^ 2) (d := (_root_.YangMills.Construction.TorusFields.supDist p.1.1 o : ℝ)) (v := v) (y := y) (ω := ω) (b := B q * y)
          (B := B q)
          (Pl := ((plaquettePathBonds o p.1.1 p.1.2.1 p.1.2.2).length : ℝ)) (l := ((plaquetteBonds p.1.1 p.1.2.1 p.1.2.2).length : ℝ))
          (t := (B (10 * q) * y / ε) ^ 20) (T := T q) (m1 := (m : ℝ) - 1) hK hdn hv hy hy1 hω hωy (hB q) rfl (by positivity)
          (plaquettePathBonds_length_le hA R.params o _ _ _) (by simp [plaquetteBonds]) (ht q) (hT q) (by linarith) (by linarith) hs2
        refine hn.trans (mul_le_mul_of_nonneg_right ?_ hvy)
        unfold momentConstant
        have a := hB q
        linarith
    · have e : xh * (momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q * (v + y)) =
          momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q * (xh * v + xh * y) := by ring
      rw [e, hxy]
      ring
  · have hBq := hB q
    refine (weightedCurvatureNorm_le _ ωf hω1 _ _ (v / 16 + 4 * (B q * y)) xh hxh (by positivity) fun p => ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · exact free_moment hMl hCo hL Xc hXc E p q hq (B q * y) (B (10 * q) * y) (mul_nonneg (hB q) hy)
        (mul_nonneg (hB _) hy) (hmom q hq) (hm'of q hq)
    · have e : xh * (v / 16 + 4 * (B q * y)) = xh * v / 16 + 4 * B q * (xh * y) := by ring
      rw [e, hxy]
      have hxv : 0 ≤ xh * v := by positivity
      have h1 : 1 + 4 * B q ≤ momentConstant (2 * 10 ^ 5 * κ ^ 2) B T q := by
        unfold momentConstant
        have b := hT q
        have c : 0 ≤ 2 * 10 ^ 5 * κ ^ 2 * (2 + 28 * B q) ^ 2 := by positivity
        linarith
      exact free_constant_aux hxv hBq h1
private theorem measure_ge_le_of_moment {Y : Type} [MeasurableSpace Y] (μ₀ : Measure Y) (f : Y → ℝ) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y)
    (k : ℕ) (ε Q : ℝ) (hε : 0 < ε) (hQ : 0 ≤ Q) (hm : ∫⁻ y, ENNReal.ofReal (f y ^ (2 * k)) ∂μ₀ ≤ ENNReal.ofReal Q) :
    μ₀ {y | ε ≤ f y} ≤ ENNReal.ofReal (Q / ε ^ (2 * k)) := by
  have hpos : 0 < ε ^ (2 * k) := by positivity
  have hsub : {y | ε ≤ f y} ⊆ {y | ENNReal.ofReal (ε ^ (2 * k)) ≤ ENNReal.ofReal (f y ^ (2 * k))} := fun y hy =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hy _)
  refine (measure_mono hsub).trans ?_
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (f y ^ (2 * k))) μ₀ := (hf.pow_const _).ennreal_ofReal.aemeasurable
  have hne : ENNReal.ofReal (ε ^ (2 * k)) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  refine (meas_ge_le_lintegral_div hmeas hne ENNReal.ofReal_ne_top).trans ?_
  rw [ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.div_le_div_right hm _
private theorem lintegral_freeCoordSize_pow_le (s : ChartSetting R n) (μ₀ : Measure (FreeCoords s.free)) (k : ℕ) (hk : 1 ≤ k) (Q : ℝ)
    (hm : ∀ b, ∫⁻ η, ENNReal.ofReal (coordNorm (η b) ^ (2 * k)) ∂μ₀ ≤ ENNReal.ofReal Q) (c : TorusBond (n * R.params.side)) :
    ∫⁻ η, ENNReal.ofReal (freeCoordSize s η c ^ (2 * k)) ∂μ₀ ≤ ENNReal.ofReal Q := by
  classical
  by_cases h : c ∈ s.free
  · have e : (fun η : FreeCoords s.free => ENNReal.ofReal (freeCoordSize s η c ^ (2 * k))) =
        fun η => ENNReal.ofReal (coordNorm (η ⟨c, h⟩) ^ (2 * k)) := by
      funext η
      unfold freeCoordSize
      rw [dif_pos h]
    rw [e]
    exact hm _
  · have e : (fun η : FreeCoords s.free => ENNReal.ofReal (freeCoordSize s η c ^ (2 * k))) = fun _ => 0 := by
      funext η
      unfold freeCoordSize
      rw [dif_neg h, zero_pow (by omega)]
      simp
    rw [e]
    simp
end Law
end ColdFineFieldAux
set_option maxHeartbeats 8000000 in
open ColdFineFieldAux in
theorem coldFineField_proof (hCut : goodConfigCutoffStatement) (hWin : scaleWindowStatement)
    (hFN : framesNearResponseStatement) (hFF : fineFieldOverCutTopStatement) (hMo : coldGroundMomentsStatement)
    (hP : cutoffCurlOverReferenceStatement) (hA : axialGaugePathBoundsStatement) (hMl : momentBoundStatement)
    (hCo : colourFormIdentitiesStatement) (hJ : parameterStatementsCombine) : coldFineFieldStatement := by
  obtain ⟨j1, j2, j3, -⟩ := hJ
  unfold goodConfigCutoffStatement ForAllPoints at hCut
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold framesNearResponseStatement at hFN
  unfold coldFineFieldStatement ForAllPoints
  refine j2 _ _ (fun Λ hf h => ?_) (j1 _ _ hCut (j1 _ _ hWin (j1 _ _ hFN (j3 coldGroundMomentsAt hMo))))
  obtain ⟨⟨Cc, cc, Xc, hcc, hyc, hCS⟩, ⟨Cv, cv, Xw, hcv, hyw, hW⟩, ⟨κ, X₁, hκ, hX₁, hFNs⟩, hMom⟩ := h
  unfold coldGroundMomentsAt at hMom
  choose Cm hCm0 hCm using hMom
  have hσ0 : 0 < Λ.table.threshold := hf.assignment_admissible.σ_pos
  have hσ1 : Λ.table.threshold ≤ 1 := hf.assignment_admissible.σ_one
  have hodd : Odd Λ.stepParams.side := hf.assignment_admissible.L_odd
  obtain ⟨Z₀, hZ₀, hnum⟩ := exists_large_scale (100 * κ ^ 2) κ Λ.table.threshold (by positivity) (by linarith) hσ0
  obtain ⟨X₂, hX₂, hlog⟩ := exists_log_le_half (Cv 0)
  obtain ⟨Zb, hZb⟩ : ∃ Zb : ℝ, Zb = max Z₀ (Λ.table.n₀ : ℝ) := ⟨_, rfl⟩
  have hZb0 : 200 ≤ Zb := hZ₀.trans (by rw [hZb]; exact le_max_left _ _)
  obtain ⟨Bm, hBm⟩ : ∃ Bm : ℕ → ℝ, Bm = fun q => 2 * (|Cm q| + 1) := ⟨_, rfl⟩
  obtain ⟨Tm, hTm⟩ : ∃ Tm : ℕ → ℝ, Tm = fun q => Bm (10 * q) ^ 20 := ⟨_, rfl⟩
  have hBm0 : ∀ q, 0 ≤ Bm q := fun q => by rw [hBm]; positivity
  have hTm0 : ∀ q, 0 ≤ Tm q := fun q => by
    rw [hTm]
    have := hBm0 (10 * q)
    positivity
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = 2 * 10 ^ 5 * (100 * κ ^ 2) ^ 2 := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hcf0 : ∀ k, 0 ≤ momentConstant Kc Bm Tm k := fun k => by
    have a := hBm0 k
    have b := hTm0 k
    unfold momentConstant
    positivity
  obtain ⟨Ci, hCi⟩ : ∃ Ci : ℕ → ℝ, Ci = fun N => 4 * 17 ^ 4 * 2 ^ (5 * N + 10) * Cm (5 * N + 10) := ⟨_, rfl⟩
  have hCi0 : ∀ N, 0 ≤ Ci N := fun N => by
    rw [hCi]
    have := hCm0 (5 * N + 10)
    positivity
  refine ⟨fun k => momentConstant Kc Bm Tm k + Ci k, 1, max (max Xc Xw) (max X₁ (max X₂ (max Λ.floor (Zb ^ 100)))), one_pos, ?_,
    fun S hx d n _ hd hn V Y hg => ?_⟩
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _) |>.trans (le_max_right _ _)
  have hxc : Xc ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxw : Xw ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : X₁ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : X₂ ≤ S.scaleCoupling := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxZ : Zb ^ 100 ≤ S.scaleCoupling :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxpos : 0 < S.scaleCoupling := by linarith
  obtain ⟨-, w2, -, -, -, w6, w7⟩ := hW S hxw
  obtain ⟨hu1, -⟩ := w7 (S.lastSeparated + d) (by omega) (by omega)
  obtain ⟨-, hu2⟩ := w7 (S.lastSeparated + d + 1) (by omega) (by omega)
  have hK' : S.lastSeparated + d ≤ S.data.windowLevel := by omega
  have hz := S.onFlow (S.lastSeparated + d) hK'
  rw [← S.stage_eq (S.lastSeparated + d) hK'] at hz
  have hRx : (S.tower.stage (S.lastSeparated + d)).coupling = S.coupling (S.lastSeparated + d) := hz.coupling_eq
  have hOn := hz.onFamily.onFamily
  have hlogx := hlog S.scaleCoupling hx2
  have hu1' : |S.coupling (S.lastSeparated + d) - S.scaleCoupling| ≤ S.scaleCoupling / 2 := by
    refine hu1.trans (le_trans ?_ hlogx)
    have h0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg (by linarith)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) h0
  have hua := abs_le.1 hu1'
  have hxuR : S.scaleCoupling / 2 ≤ (S.tower.stage (S.lastSeparated + d)).coupling := by
    rw [hRx]
    linarith [hua.1]
  have hxR0 : 0 < (S.tower.stage (S.lastSeparated + d)).coupling := by linarith [(by positivity : 0 < S.scaleCoupling / 2)]
  obtain ⟨z, hzd⟩ : ∃ z : ℝ, z = S.scaleCoupling ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hzx : S.scaleCoupling = z ^ 100 := by
    rw [hzd, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hzZ : Zb ≤ z := by
    have h0 : 0 ≤ Zb := by linarith
    rw [hzx] at hxZ
    have hz0' : 0 ≤ z := by rw [hzd]; positivity
    exact le_of_pow_le_pow_left₀ (by norm_num) hz0' hxZ
  have hzZ₀ : Z₀ ≤ z := (by rw [hZb]; exact le_max_left _ _ : Z₀ ≤ Zb).trans hzZ
  have hzn₀ : (Λ.table.n₀ : ℝ) ≤ z := (by rw [hZb]; exact le_max_right _ _ : (Λ.table.n₀ : ℝ) ≤ Zb).trans hzZ
  have hz200 : 200 ≤ z := hZb0.trans hzZ
  have hz0 : 0 < z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have h4 : S.scaleCoupling ^ (-(1 / 4) : ℝ) = (z ^ 25)⁻¹ := by
    have := rpow_neg_div_hundred S.scaleCoupling hxpos 25
    rw [← hzd] at this
    rw [← this]
    norm_num
  have h2 : S.scaleCoupling ^ (-2 : ℝ) = (z ^ 200)⁻¹ := by
    have := rpow_neg_div_hundred S.scaleCoupling hxpos 200
    rw [← hzd] at this
    rw [← this]
    norm_num
  have h12 : S.scaleCoupling ^ (-(1 / 2) : ℝ) = (z ^ 50)⁻¹ := by
    have := rpow_neg_div_hundred S.scaleCoupling hxpos 50
    rw [← hzd] at this
    rw [← this]
    norm_num
  have hp12 : S.scaleCoupling ^ ((1 : ℝ) / 2) = z ^ 50 := by
    rw [hzd, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hnbig : z ^ 50 ≤ (n : ℝ) := by
    have h2N : z ^ 50 ≤ (2 : ℝ) ^ S.logIndex := by
      have e1 : (2 : ℝ) ^ (-(S.logIndex : ℝ)) = ((2 : ℝ) ^ S.logIndex)⁻¹ := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      rw [e1, h12] at w2
      exact (inv_le_inv₀ (by positivity) (by positivity)).1 w2
    have hL2 : (2 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by
      have h40 : 2 ^ 40 ≤ Λ.table.side := hf.assignment_admissible.L_ge
      have : 2 ≤ Λ.stepParams.side := le_trans (by norm_num) h40
      exact_mod_cast this
    have h3 : (2 : ℝ) ^ S.logIndex ≤ (Λ.stepParams.side : ℝ) ^ S.logIndex := pow_le_pow_left₀ (by norm_num) hL2 _
    have h4' : ((Λ.stepParams.side ^ S.logIndex : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [hn]
      exact_mod_cast hu2
    push_cast at h4'
    linarith
  have hz50 : z ≤ z ^ 50 := le_self_pow₀ hz1 (by norm_num)
  have hn₀ : Λ.table.n₀ ≤ n := by
    have : (Λ.table.n₀ : ℝ) ≤ (n : ℝ) := (hzn₀.trans hz50).trans hnbig
    exact_mod_cast this
  have hn200 : 2 ≤ n := by
    have : (2 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨-, -, c3, -⟩ := hCS S hxc (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hg
  have hv0 : 0 ≤ (S.localCurvature (S.lastSeparated + d + 1) n V) := Real.iSup_nonneg fun p => norm_nonneg _
  have hvs : (S.localCurvature (S.lastSeparated + d + 1) n V) ≤ (z ^ 25)⁻¹ := by
    rw [← h4]
    exact hg.curvature_le
  have hr1 : z ≤ (S.range : ℝ) := by
    have : S.range = ⌈z⌉₊ := by
      show ⌈S.scaleCoupling ^ ((1 : ℝ) / 100)⌉₊ = _
      rw [hzd]
    rw [this]
    exact Nat.le_ceil z
  have hr2 : (S.range : ℝ) ≤ 2 * z := by
    have : S.range = ⌈z⌉₊ := by
      show ⌈S.scaleCoupling ^ ((1 : ℝ) / 100)⌉₊ = _
      rw [hzd]
    rw [this]
    have := Nat.ceil_lt_add_one hz0.le
    linarith
  have hmR : (S.rangeSq : ℝ) ≤ 4 * z ^ 2 := by
    have e : (S.rangeSq : ℝ) = (S.range : ℝ) ^ 2 := by
      show ((S.range ^ 2 : ℕ) : ℝ) = _
      push_cast
      ring
    rw [e]
    calc (S.range : ℝ) ^ 2 ≤ (2 * z) ^ 2 := pow_le_pow_left₀ (by positivity) hr2 2
      _ = _ := by ring
  have hm2 : 2 ≤ S.rangeSq := by
    have e : (S.rangeSq : ℝ) = (S.range : ℝ) ^ 2 := by
      show ((S.range ^ 2 : ℕ) : ℝ) = _
      push_cast
      ring
    have : (2 : ℝ) ≤ (S.rangeSq : ℝ) := by
      rw [e]
      calc (2 : ℝ) ≤ z := (by norm_num : (2 : ℝ) ≤ 200).trans hz200
        _ ≤ z ^ 2 := le_self_pow₀ hz1 (by norm_num)
        _ ≤ (S.range : ℝ) ^ 2 := pow_le_pow_left₀ hz0.le hr1 2
    exact_mod_cast this
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hnum z (S.rangeSq : ℝ) (S.localCurvature (S.lastSeparated + d + 1) n V) hzZ₀ (by positivity) hmR hv0 hvs
  have hNear := hFNs S hx1 d n hd hn V Y hg
  have hρ0 : 0 ≤ (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius := by
    show 0 ≤ Λ.table.threshold / 64
    positivity
  have hρ1 : (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius ≤ 1 / 64 := by
    show Λ.table.threshold / 64 ≤ 1 / 64
    linarith
  have hz3 : (200 : ℝ) ≤ z ^ 200 := hz200.trans (le_self_pow₀ hz1 (by norm_num))
  have hω0 : 0 ≤ S.scaleCoupling ^ (-2 : ℝ) := by positivity
  have hω1 : S.scaleCoupling ^ (-2 : ℝ) ≤ 1 / 64 := by
    rw [h2, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hsmF : κ * ((((2 * S.rangeSq + 6 : ℕ) : ℝ) + 1) * (S.localCurvature (S.lastSeparated + d + 1) n V)) ≤ 1 / 64 := by
    push_cast
    exact n2
  have hOver := hFF (S.tower.stage (S.lastSeparated + d)).toStepSetup n (S.cutoffLie (S.lastSeparated + d + 1) n V)
    (responseOfLieForm Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d) (S.cutoffLie (S.lastSeparated + d + 1) n V))
    (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq + 6) (S.localCurvature (S.lastSeparated + d + 1) n V)
    (S.scaleCoupling ^ (-2 : ℝ)) κ hodd hn200 hNear hκ hv0 hω0 hω1 hρ0 hρ1 hsmF
  have hcold : TorusFields.IsCold Λ.table.threshold (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)) := fun x μ ν h => by
    refine (c3 1 zero_le_one le_rfl x μ ν h).trans_lt ?_
    linarith
  have hM := fun q => hCm q (S.tower.stage (S.lastSeparated + d)).toStepSetup hOn hxR0 n hn₀
    (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)) hcold
  have hside : 2 * (2 * S.rangeSq + 6) + 2 < n * Λ.stepParams.side := by
    have h1 : ((2 * (2 * S.rangeSq + 6) + 2 : ℕ) : ℝ) < (n : ℝ) := by
      push_cast
      linarith
    have h2' : 2 * (2 * S.rangeSq + 6) + 2 < n := by exact_mod_cast h1
    have h3 : 1 ≤ Λ.stepParams.side := by
      have := hf.assignment_admissible.L_ge
      exact le_trans (by norm_num) this
    exact lt_of_lt_of_le h2' (Nat.le_mul_of_pos_right n h3)
  have hv1 : (S.localCurvature (S.lastSeparated + d + 1) n V) ≤ 1 := by
    refine hvs.trans ?_
    rw [← one_div]
    have : (1 : ℝ) ≤ z ^ 25 := one_le_pow₀ hz1
    exact (div_le_one (by positivity)).2 this
  have hsmall : 10 ^ 4 * (100 * κ ^ 2) ^ 2 * (((2 * S.rangeSq + 6 : ℕ) : ℝ) + 3) ^ 2 *
      ((S.localCurvature (S.lastSeparated + d + 1) n V) + S.scaleCoupling ^ (-2 : ℝ) +
        100 * (((2 * S.rangeSq + 6 : ℕ) : ℝ) + 3) * (z ^ 30)⁻¹) ≤ 1 := by
    push_cast
    rw [h2]
    exact n1
  have hL : ColdLawData (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.cutoffLie (S.lastSeparated + d + 1) n V)
      (responseOfLieForm Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d) (S.cutoffLie (S.lastSeparated + d + 1) n V))
      (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq + 6) (S.localCurvature (S.lastSeparated + d + 1) n V)
      (S.scaleCoupling ^ (-2 : ℝ)) (100 * κ ^ 2) (z ^ 30)⁻¹ :=
    ⟨hOver, (hM 1).1, (hM 1).2.1, hρ1, (one_le_pow₀ hκ).trans (le_mul_of_one_le_left (sq_nonneg κ) (by norm_num)), hv0, hv1, hω0, by positivity, hside, hsmall⟩
  have hy0 : 0 ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) := by positivity
  have hy1 : S.scaleCoupling ^ (-(1 / 2) : ℝ) ≤ 1 := by
    rw [h12, ← one_div]
    have : (1 : ℝ) ≤ z ^ 50 := one_le_pow₀ hz1
    exact (div_le_one (by positivity)).2 this
  have hxy : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) = 1 := by
    rw [h12, hp12]
    exact mul_inv_cancel₀ (by positivity)
  have hωy : S.scaleCoupling ^ (-2 : ℝ) ≤ (S.scaleCoupling ^ (-(1 / 2) : ℝ)) ^ 2 := by
    rw [h2, h12, inv_pow, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hz1 (by norm_num))
  have hsq : (1 + 2 * (S.rangeSq : ℝ)) ^ 2 * ((S.localCurvature (S.lastSeparated + d + 1) n V) + S.scaleCoupling ^ (-(1 / 2) : ℝ)) ≤ 1 := by
    rw [h12]
    exact n6
  have hxu2 : (S.tower.stage (S.lastSeparated + d)).coupling ^ (-(1 / 2) : ℝ) ≤ 2 * S.scaleCoupling ^ (-(1 / 2) : ℝ) := by
    have a1 : (z ^ 50 / 2) ^ 2 ≤ (S.tower.stage (S.lastSeparated + d)).coupling := by
      have e : (z ^ 50 / 2) ^ 2 = S.scaleCoupling / 4 := by
        rw [hzx]
        ring
      rw [e]
      linarith [(by positivity : 0 < S.scaleCoupling / 4)]
    have a2 : z ^ 50 / 2 ≤ (S.tower.stage (S.lastSeparated + d)).coupling ^ ((1 : ℝ) / 2) := by
      have b1 := Real.rpow_le_rpow (by positivity) a1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)] at b1
      exact b1
    rw [Real.rpow_neg hxR0.le]
    have a3 := inv_anti₀ (by positivity) a2
    refine a3.trans (le_of_eq ?_)
    rw [h12]
    field_simp
  have hmom : ∀ q : ℕ, 1 ≤ q → ∀ c : TorusBond (n * ((S.tower.stage (S.lastSeparated + d)).toStepSetup).params.side),
      eLpNorm (fun η => freeCoordSize (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) η c) ((2 * q : ℕ) : ENNReal)
      (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) ≤
        ENNReal.ofReal (Bm q * S.scaleCoupling ^ (-(1 / 2) : ℝ)) := by
    intro q hq c
    have a := hMl.2 _ (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)))
      (fun η => freeCoordSize (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) η c) q (Cm q) (S.tower.stage (S.lastSeparated + d)).coupling hq hxR0
      (fun η => freeCoordSize_nonneg _ η c)
      (lintegral_freeCoordSize_pow_le _ _ q hq _ (hM q).2.2 c)
    refine a.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hBm]
    have h0 : 0 ≤ |Cm q| + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hxu2 h0
    calc _ ≤ _ := this
      _ = _ := by ring
  have ht : ∀ q, (Bm (10 * q) * S.scaleCoupling ^ (-(1 / 2) : ℝ) / (z ^ 30)⁻¹) ^ 20 ≤
      Tm q * (S.scaleCoupling ^ (-(1 / 2) : ℝ)) ^ 2 := by
    intro q
    have hB := hBm0 (10 * q)
    rw [h12, hTm]
    have e : Bm (10 * q) * (z ^ 50)⁻¹ / (z ^ 30)⁻¹ = Bm (10 * q) * (z ^ 20)⁻¹ := by
      field_simp
    rw [e, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hz1 (by norm_num))
  have hXc : pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
      (S.cutoffColourForm (S.lastSeparated + d + 1) n V) =
      toColourForm (responseOfLieForm Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
        (S.cutoffLie (S.lastSeparated + d + 1) n V)) :=
    hCo.2.1 Λ.stepParams.side n Λ.stepParams.coupling Λ.table.ρA (S.lastSeparated + d) (S.cutoffLie (S.lastSeparated + d + 1) n V)
  have hom : ∀ p, S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p ≤ 1 := by
    intro p
    have hrate : 0 ≤ Λ.stepParams.weightRate := by
      have := hf.assignment_admissible.rt_pos
      show 0 ≤ Λ.table.rt / 2 ^ 10
      positivity
    unfold MomentPoint.distanceWeight
    apply Real.exp_le_one_iff.2
    have : 0 ≤ Λ.stepParams.weightRate / 8 *
        max 0 ((TorusFields.supDist p.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) - (S.radius : ℝ)) := by positivity
    linarith
  have hcl := moment_conditions hP hA hMl hCo hL hρ0 S.rangeSq hm2 rfl _ hXc (S.scaleCoupling ^ (-(1 / 2) : ℝ))
    (S.scaleCoupling ^ ((1 : ℝ) / 2)) hy0 hy1 (by positivity) hxy
    hωy hsq Bm Tm hBm0 hTm0 hmom ht
    {η | boxCurvature (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq)
      ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))).field η) ≤
        S.scaleCoupling ^ (-(1 / 4) : ℝ)}
    (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) hom
  rw [← hKc] at hcl
  refine ⟨fun N => ?_, fun p q hq hdp => ?_, fun q hq => ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 5 * N + 10 := ⟨_, rfl⟩
    have hk1 : 1 ≤ k := by omega
    have hε : 0 < (z ^ 30)⁻¹ := by positivity
    have hCk := hCm0 k
    have hQ : 0 ≤ Cm k * ((S.tower.stage (S.lastSeparated + d)).coupling ^ k)⁻¹ := by positivity
    have hXb : (S.localCurvature (S.lastSeparated + d + 1) n V) / 2 + 8 * (z ^ 30)⁻¹ + 5 * S.scaleCoupling ^ (-2 : ℝ) ≤
        S.scaleCoupling ^ (-(1 / 4) : ℝ) := by
      rw [h2, h4]
      exact n4
    refine (measure_boxCurvature_gt_le hP Λ.stepParams hL S.rangeSq _ hXb (by omega)).trans ?_
    have htail : ∀ c : TorusBond (n * Λ.stepParams.side),
        (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)))
          {η | (z ^ 30)⁻¹ ≤ freeCoordSize (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
            (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) η c} ≤
        ENNReal.ofReal (Cm k * ((S.tower.stage (S.lastSeparated + d)).coupling ^ k)⁻¹ / ((z ^ 30)⁻¹) ^ (2 * k)) := fun c =>
      measure_ge_le_of_moment
        (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)))
        (fun η => freeCoordSize (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) η c)
        (measurable_freeCoordSize (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) c)
        (fun η => freeCoordSize_nonneg (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V))) η c) k _ _ hε hQ
        (lintegral_freeCoordSize_pow_le (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)))
          (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (expField 1 (S.cutoffLie (S.lastSeparated + d + 1) n V)))
          k hk1 _ (hM k).2.2 c)
    refine (Finset.sum_le_card_nsmul _ _ _ fun c _ => htail c).trans ?_
    rw [nsmul_eq_mul]
    have hT0 : 0 ≤ Cm k * ((S.tower.stage (S.lastSeparated + d)).coupling ^ k)⁻¹ / ((z ^ 30)⁻¹) ^ (2 * k) := by positivity
    have hcard : ((((TorusLumps.thickening (2 * S.rangeSq) {(S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))}) ×ˢ
        (Finset.univ : Finset (Fin 4))).card : ℕ) : ℝ) ≤ 4 * (4 * (S.rangeSq : ℝ) + 1) ^ 4 := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have a1 := TorusCounting.card_thickening_singleton_le (2 * S.rangeSq) (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
      have a2 : (((TorusLumps.thickening (2 * S.rangeSq) {(S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))}).card : ℕ) : ℝ) ≤
          (((2 * (2 * S.rangeSq) + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast a1
      push_cast at a2 ⊢
      linarith
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have a1 := mul_le_mul_of_nonneg_right hcard hT0
    have a2 := tail_count_le (m := (S.rangeSq : ℝ)) (Cm := Cm k) k N hk hz1 hzx (by positivity) hmR hCk _ hxuR
    refine a1.trans (a2.trans ?_)
    have hxN : 0 ≤ S.scaleCoupling ^ (-(N : ℝ)) := by positivity
    have hCiN : 4 * 17 ^ 4 * 2 ^ k * Cm k = Ci N := by
      rw [hCi, hk]
    rw [hCiN]
    refine mul_le_mul_of_nonneg_right ?_ hxN
    have := hcf0 N
    show Ci N ≤ momentConstant Kc Bm Tm N + Ci N
    linarith
  · refine (hcl.1 p q hq hdp).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ (1 + (TorusFields.supDist p.1.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ)) ^ 2 *
        ((S.localCurvature (S.lastSeparated + d + 1) n V) + S.scaleCoupling ^ (-(1 / 2) : ℝ)) ^ 2 := by positivity
    have h1 := hCi0 q
    have := mul_le_mul_of_nonneg_right (by linarith : momentConstant Kc Bm Tm q ≤ momentConstant Kc Bm Tm q + Ci q) h0
    calc _ = momentConstant Kc Bm Tm q * ((1 + (TorusFields.supDist p.1.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ)) ^ 2 *
          ((S.localCurvature (S.lastSeparated + d + 1) n V) + S.scaleCoupling ^ (-(1 / 2) : ℝ)) ^ 2) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · obtain ⟨q1, q2⟩ := hcl.2 q hq
    have hw : 0 ≤ 1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * (S.localCurvature (S.lastSeparated + d + 1) n V) := by positivity
    have h1 := hCi0 q
    have hle : momentConstant Kc Bm Tm q * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * (S.localCurvature (S.lastSeparated + d + 1) n V)) ≤
        (momentConstant Kc Bm Tm q + Ci q) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * (S.localCurvature (S.lastSeparated + d + 1) n V)) :=
      mul_le_mul_of_nonneg_right (by linarith) hw
    exact ⟨q1.trans (ENNReal.ofReal_le_ofReal hle), q2.trans (ENNReal.ofReal_le_ofReal hle)⟩
end MomentLaw
end YangMills.Construction
end
