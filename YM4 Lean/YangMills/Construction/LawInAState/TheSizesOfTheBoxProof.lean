import YangMills.Construction.LawInAState.MarksOnTheBoxProof
import YangMills.Construction.LawInAState.TheSizesOfTheBox
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Filter Topology
namespace YangMills.Construction.StateLaws
open YangMills.Construction.TorusLumps YangMills.Construction.BoxGaussian YangMills.Construction.QuadraticConcentration
private lemma eventually_const_le_rpow {a : ℝ} (ha : 0 < a) (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop K
private lemma eventually_log_le_mul_rpow {a : ℝ} (ha : 0 < a) {k : ℝ} (hk : 0 < k) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ k * x ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).bound hk
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have h1 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have h2 : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) _
  simpa [Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2] using hx
private lemma rpow_mul_rpow {x : ℝ} (hx : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a + b) :=
  (Real.rpow_add hx a b).symm
private lemma rpow_pow_natCast {x : ℝ} (hx : 0 < x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ ((n : ℝ) * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, mul_comm]
private lemma rpow_le_rpow_exponent {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx h
private lemma exp_mul_log_eq_rpow {x : ℝ} (hx : 0 < x) (b : ℝ) : Real.exp (b * Real.log x) = x ^ b := by
  rw [Real.rpow_def_of_pos hx, mul_comm]
private lemma boxRadius_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ^ (1 / 27 : ℝ) ≤ (boxRadius x : ℝ) ∧ (boxRadius x : ℝ) ≤ 2 * x ^ (1 / 27 : ℝ) := by apply _root_.YangMills.SharedProofs.p14121 <;> assumption
private lemma clusterRange_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ^ (1 / 100 : ℝ) ≤ (clusterRange x : ℝ) ∧ (clusterRange x : ℝ) ≤ 2 * x ^ (1 / 100 : ℝ) := by
  have h1 : 1 ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow hx (by norm_num)
  refine ⟨Nat.le_ceil _, ?_⟩
  have := Nat.ceil_lt_add_one (show 0 ≤ x ^ (1 / 100 : ℝ) by linarith)
  simp only [clusterRange]
  linarith
private lemma scale_bounds {x n L : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L) (h1 : 2 ^ 12 * (clusterRange x : ℝ) ≤ n)
    (h2 : n ≤ 2 ^ 13 * L * (clusterRange x : ℝ)) :
    x ^ (1 / 100 : ℝ) ≤ n ∧ 2 ^ 12 ≤ n ∧ n ≤ 2 ^ 14 * L * x ^ (1 / 100 : ℝ) := by
  obtain ⟨r1, r2⟩ := clusterRange_bounds hx
  have u1 : 1 ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow hx (by norm_num)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h3 : 2 ^ 13 * L * (clusterRange x : ℝ) ≤ 2 ^ 13 * L * (2 * x ^ (1 / 100 : ℝ)) :=
    mul_le_mul_of_nonneg_left r2 (by positivity)
  linarith
private lemma translateSiteBound_le {x n L : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L) (hn0 : 2 ^ 12 ≤ n)
    (hn : n ≤ 2 ^ 14 * L * x ^ (1 / 100 : ℝ)) :
    translateSiteBound n ≤ (15 * 2 ^ 14 * L) ^ 4 * x ^ (1 / 25 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h1 : 2 * n + 13 ≤ 15 * 2 ^ 14 * L * x ^ (1 / 100 : ℝ) := by nlinarith
  calc translateSiteBound n ≤ (15 * 2 ^ 14 * L * x ^ (1 / 100 : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
    _ = (15 * 2 ^ 14 * L) ^ 4 * x ^ (1 / 25 : ℝ) := by
      rw [mul_pow, rpow_pow_natCast hx0]; congr 2; norm_num
private lemma boxFlatness_nonneg {x C : ℝ} (hx : 1 ≤ x) (hC : 1 ≤ C) : 0 ≤ boxFlatness C x := by
  have hl := Real.log_nonneg hx
  have : 0 ≤ boxScale x := by unfold boxScale; positivity
  unfold boxFlatness
  positivity
private lemma two_mul_boxFlatness_le {x C : ℝ} (hx : 1 ≤ x) (hC : 1 ≤ C) (hl : Real.log x ≤ x ^ (1 / 40000 : ℝ))
    (hc : 4 * C ≤ x ^ (1 / 40000 : ℝ)) : 2 * boxFlatness C x ≤ x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl0 := Real.log_nonneg hx
  obtain ⟨w1, w2⟩ := boxRadius_bounds hx
  have hw : 0 < x ^ (1 / 27 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hR : (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) ≤ x ^ (-(2 / 81) : ℝ) := by
    have := Real.rpow_le_rpow_of_nonpos hw w1 (by norm_num : (-(2 / 3) : ℝ) ≤ 0)
    rw [← Real.rpow_mul hx0.le] at this
    convert this using 2
    norm_num
  have e : 2 * boxFlatness C x = (4 * C) * (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) * x ^ (-(1 / 2) : ℝ) *
      (Real.log x * Real.log x) := by
    simp only [boxFlatness, boxScale]; ring
  rw [e]
  calc (4 * C) * (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) * x ^ (-(1 / 2) : ℝ) * (Real.log x * Real.log x)
      ≤ x ^ (1 / 40000 : ℝ) * x ^ (-(2 / 81) : ℝ) * x ^ (-(1 / 2) : ℝ) *
          (x ^ (1 / 40000 : ℝ) * x ^ (1 / 40000 : ℝ)) := by gcongr
    _ ≤ _ := by
      rw [rpow_mul_rpow hx0, rpow_mul_rpow hx0, rpow_mul_rpow hx0, rpow_mul_rpow hx0]
      exact rpow_le_rpow_exponent hx (by norm_num)
private lemma boxMeanCurlBound_le_one {x C : ℝ} (hx : 1 ≤ x) (hC : 1 ≤ C) (hl : Real.log x ≤ x ^ (1 / 40000 : ℝ))
    (hc : 8 * C ≤ x ^ (1 / 40000 : ℝ)) : boxMeanCurlBound C x ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hl0 := Real.log_nonneg hx
  obtain ⟨w1, w2⟩ := boxRadius_bounds hx
  have e : boxMeanCurlBound C x = (C * 2) * (boxRadius x : ℝ) ^ 2 * x ^ (-(1 / 2) : ℝ) * Real.log x := by
    simp only [boxMeanCurlBound, boxScale]; ring
  rw [e]
  have h2 : (boxRadius x : ℝ) ^ 2 ≤ 4 * x ^ (2 / 27 : ℝ) := by
    calc (boxRadius x : ℝ) ^ 2 ≤ (2 * x ^ (1 / 27 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) w2 2
      _ = 4 * x ^ (2 / 27 : ℝ) := by rw [mul_pow, rpow_pow_natCast hx0]; norm_num
  calc (C * 2) * (boxRadius x : ℝ) ^ 2 * x ^ (-(1 / 2) : ℝ) * Real.log x
      ≤ (C * 2) * (4 * x ^ (2 / 27 : ℝ)) * x ^ (-(1 / 2) : ℝ) * x ^ (1 / 40000 : ℝ) := by gcongr
    _ = (8 * C) * x ^ (2 / 27 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (1 / 40000 : ℝ) := by ring
    _ ≤ x ^ (1 / 40000 : ℝ) * x ^ (2 / 27 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (1 / 40000 : ℝ) := by gcongr
    _ ≤ 1 := by
      rw [rpow_mul_rpow hx0, rpow_mul_rpow hx0, rpow_mul_rpow hx0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
private lemma exp_neg_le_rpow {x t b : ℝ} (hx : 1 ≤ x) (h : b * Real.log x ≤ t) : Real.exp (-t) ≤ x ^ (-b) := by
  have hx0 : 0 < x := by linarith
  rw [← exp_mul_log_eq_rpow hx0]
  exact Real.exp_le_exp.2 (by linarith)
private lemma farPairError_le {x n T c C G : ℝ} (hx : 1 ≤ x) (hC : 1 ≤ C) (hG : 1 ≤ G) (hT : 0 ≤ T)
    (hNc : translateSiteBound n ≤ x) (hN0 : 0 ≤ translateSiteBound n)
    (hover : farSiteOverlap T c n ≤ T * x ^ (-100 : ℝ)) (hover0 : 0 ≤ farSiteOverlap T c n)
    (htop : boxMeanCurlBound C x ≤ 1) (htop0 : 0 ≤ boxMeanCurlBound C x)
    (hK : C ^ 2 * T ^ 2 + C ^ 2 * T * G ^ 2 + C ^ 2 * G ^ 2 * T ≤ x) :
    farPairError C G T c n x ≤ x ^ (-20 : ℝ) := by
  have hx0 : 0 < x := by linarith
  set q := x ^ (-100 : ℝ) with hq
  have q0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have q1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  set N := translateSiteBound n with hN
  set o := farSiteOverlap T c n with ho
  set t := boxMeanCurlBound C x with ht
  have a1 : C ^ 2 * N ^ 2 * o ^ 2 ≤ C ^ 2 * x ^ 2 * (T ^ 2 * q) := by
    have h1 : o ^ 2 ≤ T ^ 2 * q := by
      calc o ^ 2 ≤ (T * q) ^ 2 := pow_le_pow_left₀ hover0 hover 2
        _ = T ^ 2 * (q * q) := by ring
        _ ≤ T ^ 2 * q := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_of_le_one_right q0.le q1
    gcongr
  have a2 : C ^ 2 * o * N * G ^ 2 ≤ C ^ 2 * (T * q) * x ^ 2 * G ^ 2 := by
    have h1 : N ≤ x ^ 2 := hNc.trans (by nlinarith)
    gcongr
  have a3 : t ^ 2 * C ^ 2 * G ^ 2 * N ^ 2 * o ≤ 1 ^ 2 * C ^ 2 * G ^ 2 * x ^ 2 * (T * q) := by gcongr
  have e : farPairError C G T c n x =
      C ^ 2 * N ^ 2 * o ^ 2 + C ^ 2 * o * N * G ^ 2 + t ^ 2 * C ^ 2 * G ^ 2 * N ^ 2 * o := rfl
  rw [e]
  have h3 : x ^ 2 * q * x ≤ x ^ (-20 : ℝ) := by
    have : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
    rw [this, hq, rpow_mul_rpow hx0]
    nth_rewrite 2 [show x = x ^ (1 : ℝ) from (Real.rpow_one x).symm]
    rw [rpow_mul_rpow hx0]
    exact rpow_le_rpow_exponent hx (by norm_num)
  have h4 : (C ^ 2 * T ^ 2 + C ^ 2 * T * G ^ 2 + C ^ 2 * G ^ 2 * T) * (x ^ 2 * q) ≤ x * (x ^ 2 * q) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  nlinarith
private lemma nearPairShare_le {x n L : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L) (hn0 : 2 ^ 12 ≤ n)
    (hn : n ≤ 2 ^ 14 * L * x ^ (1 / 100 : ℝ)) (hK : (16 * (9 * 2 ^ 14 * L)) ^ 4 ≤ x ^ (1 / 5000 : ℝ)) :
    nearPairShare n x ≤ x ^ (2 * (1 / 50 - 2 / 27 + 1 / 10000) : ℝ) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨w1, w2⟩ := boxRadius_bounds hx
  have hB : 2 * (nearTranslateRadius n : ℝ) + 1 ≤ 9 * 2 ^ 14 * L * x ^ (1 / 100 : ℝ) := by
    have h1 : (⌈3 * n⌉₊ : ℝ) < 3 * n + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : (nearTranslateRadius n : ℝ) = (⌈3 * n⌉₊ : ℝ) + 12 := by simp [nearTranslateRadius]
    rw [h2]
    nlinarith
  have hm : x ^ (1 / 27 : ℝ) / 16 ≤ 2 * (averagingRadius x : ℝ) + 1 := by
    have h1 : boxRadius x < 16 * (averagingRadius x + 1) := by
      simp only [averagingRadius]
      have := Nat.div_add_mod (boxRadius x) 16
      have h2 := Nat.mod_lt (boxRadius x) (by norm_num : 16 > 0)
      omega
    have h3 : (boxRadius x : ℝ) < 16 * ((averagingRadius x : ℝ) + 1) := by exact_mod_cast h1
    linarith
  unfold nearPairShare
  rw [div_le_iff₀ (by positivity)]
  calc (2 * (nearTranslateRadius n : ℝ) + 1) ^ 4 ≤ (9 * 2 ^ 14 * L * x ^ (1 / 100 : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hB 4
    _ = (9 * 2 ^ 14 * L) ^ 4 * x ^ (1 / 25 : ℝ) := by
      rw [mul_pow, rpow_pow_natCast hx0]; congr 2; norm_num
    _ ≤ x ^ (2 * (1 / 50 - 2 / 27 + 1 / 10000) : ℝ) * (x ^ (1 / 27 : ℝ) / 16) ^ 4 := by
      have e1 : (x ^ (1 / 27 : ℝ) / 16) ^ 4 = x ^ (4 / 27 : ℝ) / 16 ^ 4 := by
        rw [div_pow, rpow_pow_natCast hx0]; congr 2; norm_num
      rw [e1]
      have e2 : x ^ (2 * (1 / 50 - 2 / 27 + 1 / 10000) : ℝ) * (x ^ (4 / 27 : ℝ) / 16 ^ 4) =
          x ^ (1 / 5000 : ℝ) * x ^ (1 / 25 : ℝ) / 16 ^ 4 := by
        rw [mul_div_assoc', rpow_mul_rpow hx0, rpow_mul_rpow hx0]; congr 2; norm_num
      rw [e2, le_div_iff₀ (by positivity)]
      have : 0 < x ^ (1 / 25 : ℝ) := Real.rpow_pos_of_pos hx0 _
      have h5 : (16 * (9 * 2 ^ 14 * L)) ^ 4 = (9 * 2 ^ 14 * L) ^ 4 * 16 ^ 4 := by ring
      rw [h5] at hK
      nlinarith
    _ ≤ x ^ (2 * (1 / 50 - 2 / 27 + 1 / 10000) : ℝ) * (2 * (averagingRadius x : ℝ) + 1) ^ 4 := by gcongr
private lemma logWeightBound_le {x C : ℝ} (hx : 1 ≤ x) (hC : 1 ≤ C) (hl : Real.log x ≤ x ^ (1 / 40000 : ℝ))
    (hc : 16 * (2 ^ 9 * C) ≤ x ^ (1 / 40000 : ℝ)) : 16 * logWeightBound C x ≤ x ^ (-(1 / 7) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl0 := Real.log_nonneg hx
  obtain ⟨w1, w2⟩ := boxRadius_bounds hx
  have h9 : (boxRadius x : ℝ) ^ 9 ≤ 2 ^ 9 * x ^ (1 / 3 : ℝ) := by
    calc (boxRadius x : ℝ) ^ 9 ≤ (2 * x ^ (1 / 27 : ℝ)) ^ 9 := pow_le_pow_left₀ (by positivity) w2 9
      _ = 2 ^ 9 * x ^ (1 / 3 : ℝ) := by rw [mul_pow, rpow_pow_natCast hx0]; congr 2; norm_num
  have e3 : Real.log x ^ 3 ≤ x ^ (3 / 40000 : ℝ) := by
    calc Real.log x ^ 3 ≤ (x ^ (1 / 40000 : ℝ)) ^ 3 := pow_le_pow_left₀ hl0 hl 3
      _ = x ^ (3 / 40000 : ℝ) := by rw [rpow_pow_natCast hx0]; congr 1; norm_num
  calc 16 * logWeightBound C x = 16 * (C * (boxRadius x : ℝ) ^ 9 * x ^ (-(1 / 2) : ℝ) * Real.log x ^ 3) := rfl
    _ ≤ 16 * (C * (2 ^ 9 * x ^ (1 / 3 : ℝ)) * x ^ (-(1 / 2) : ℝ) * x ^ (3 / 40000 : ℝ)) := by gcongr
    _ = (16 * (2 ^ 9 * C)) * x ^ (1 / 3 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (3 / 40000 : ℝ) := by ring
    _ ≤ x ^ (1 / 40000 : ℝ) * x ^ (1 / 3 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (3 / 40000 : ℝ) := by gcongr
    _ ≤ _ := by
      rw [rpow_mul_rpow hx0, rpow_mul_rpow hx0, rpow_mul_rpow hx0]
      exact rpow_le_rpow_exponent hx (by norm_num)
private lemma marksRemainder_le {x n C c L : ℝ} (hx : 1 ≤ x) (hC : 1 ≤ C) (hc0 : 0 < c) (hL : 1 ≤ L) (hn0 : 0 ≤ n)
    (hn : n ≤ 2 ^ 14 * L * x ^ (1 / 100 : ℝ)) (hl : Real.log x ≤ x ^ (1 / 40000 : ℝ))
    (hc : 2 * (C * (2 ^ 14 * L) ^ 4 * 2 ^ 8 * 8) ≤ x ^ (1 / 40000 : ℝ)) (h2 : 2 * Real.log x ≤ c * (boxRadius x : ℝ))
    (hx2 : 2 ≤ x ^ (9 / 10 : ℝ)) :
    marksRemainder C c n x ≤ x ^ (-(11 / 10) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl0 := Real.log_nonneg hx
  obtain ⟨w1, w2⟩ := boxRadius_bounds hx
  have h8 : (boxRadius x : ℝ) ^ 8 ≤ 2 ^ 8 * x ^ (8 / 27 : ℝ) := by
    calc (boxRadius x : ℝ) ^ 8 ≤ (2 * x ^ (1 / 27 : ℝ)) ^ 8 := pow_le_pow_left₀ (by positivity) w2 8
      _ = 2 ^ 8 * x ^ (8 / 27 : ℝ) := by rw [mul_pow, rpow_pow_natCast hx0]; congr 2; norm_num
  have hn4 : n ^ 4 ≤ (2 ^ 14 * L) ^ 4 * x ^ (1 / 25 : ℝ) := by
    calc n ^ 4 ≤ (2 ^ 14 * L * x ^ (1 / 100 : ℝ)) ^ 4 := pow_le_pow_left₀ hn0 hn 4
      _ = _ := by rw [mul_pow, rpow_pow_natCast hx0]; congr 2; norm_num
  have hd : boxScale x ^ 3 ≤ 8 * x ^ (-(3 / 2) : ℝ) * x ^ (3 / 40000 : ℝ) := by
    have e3 : Real.log x ^ 3 ≤ x ^ (3 / 40000 : ℝ) := by
      calc Real.log x ^ 3 ≤ (x ^ (1 / 40000 : ℝ)) ^ 3 := pow_le_pow_left₀ hl0 hl 3
        _ = x ^ (3 / 40000 : ℝ) := by rw [rpow_pow_natCast hx0]; congr 1; norm_num
    have e4 : boxScale x ^ 3 = 8 * x ^ (-(3 / 2) : ℝ) * Real.log x ^ 3 := by
      simp only [boxScale]
      rw [mul_pow, mul_pow, rpow_pow_natCast hx0]
      norm_num
    rw [e4]
    gcongr
  have hs0 : 0 ≤ boxScale x := by unfold boxScale; positivity
  have p1 : C * n ^ 4 * (boxRadius x : ℝ) ^ 8 * boxScale x ^ 3 ≤ (1 / 2) * x ^ (-(11 / 10) : ℝ) := by
    calc C * n ^ 4 * (boxRadius x : ℝ) ^ 8 * boxScale x ^ 3
        ≤ C * ((2 ^ 14 * L) ^ 4 * x ^ (1 / 25 : ℝ)) * (2 ^ 8 * x ^ (8 / 27 : ℝ)) *
            (8 * x ^ (-(3 / 2) : ℝ) * x ^ (3 / 40000 : ℝ)) := by gcongr
      _ = (1 / 2) * (2 * (C * (2 ^ 14 * L) ^ 4 * 2 ^ 8 * 8)) *
            (x ^ (1 / 25 : ℝ) * x ^ (8 / 27 : ℝ) * x ^ (-(3 / 2) : ℝ) * x ^ (3 / 40000 : ℝ)) := by ring
      _ ≤ (1 / 2) * x ^ (1 / 40000 : ℝ) *
            (x ^ (1 / 25 : ℝ) * x ^ (8 / 27 : ℝ) * x ^ (-(3 / 2) : ℝ) * x ^ (3 / 40000 : ℝ)) := by gcongr
      _ ≤ _ := by
        rw [rpow_mul_rpow hx0, rpow_mul_rpow hx0, rpow_mul_rpow hx0, mul_assoc, rpow_mul_rpow hx0]
        have := rpow_le_rpow_exponent hx
          (show (1 / 40000 + (1 / 25 + 8 / 27 + -(3 / 2) + 3 / 40000) : ℝ) ≤ -(11 / 10) by norm_num)
        linarith
  have p2 : Real.exp (-(c * (boxRadius x : ℝ))) ≤ (1 / 2) * x ^ (-(11 / 10) : ℝ) := by
    have h3 := exp_neg_le_rpow (b := 2) hx h2
    have h4 : x ^ (-2 : ℝ) * 2 ≤ x ^ (-2 : ℝ) * x ^ (9 / 10 : ℝ) := by
      have := Real.rpow_pos_of_pos hx0 (-2 : ℝ)
      gcongr
    rw [rpow_mul_rpow hx0] at h4
    have e : (-2 + 9 / 10 : ℝ) = -(11 / 10) := by norm_num
    rw [e] at h4
    linarith
  unfold marksRemainder
  linarith
private lemma one_add_four_mul_le {t u : ℝ} (t0 : 0 ≤ t) (t1 : t ≤ 1 / 16) (u0 : 0 < u) (u1 : u ≤ 1 / 32) :
    1 + 4 * t ≤ (1 + (8 * t + 8 * u)) * (1 - u) := by nlinarith
private lemma exp_two_mul_le {t : ℝ} (t0 : 0 ≤ t) (t1 : t ≤ 1 / 16) : Real.exp (2 * t) ≤ 1 + 4 * t := by
  have h3 := Real.exp_bound_div_one_sub_of_interval (x := 2 * t) (by positivity) (by linarith)
  refine h3.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith
set_option maxHeartbeats 1600000 in
theorem boxSizesStatement_holds : boxSizesStatement := by
  intro C c G T L Cm R₀ hC hc hG hT hL hCm
  have s40 : (0 : ℝ) < 1 / 40000 := by norm_num
  have s27 : (0 : ℝ) < 1 / 27 := by norm_num
  set K₁ : ℝ := 15 * 2 ^ 14 * L with hK₁
  set Kc : ℝ := C ^ 2 * G ^ 4 + C * G ^ 2 + 1 with hKc
  have ev : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ Real.exp 1 ≤ x ∧ Real.log x ≤ 1 * x ^ (1 / 40000 : ℝ) ∧
      8 * C ≤ x ^ (1 / 40000 : ℝ) ∧ 16 * (2 ^ 9 * C) ≤ x ^ (1 / 40000 : ℝ) ∧
      2 * (C * (2 ^ 14 * L) ^ 4 * 2 ^ 8 * 8) ≤ x ^ (1 / 40000 : ℝ) ∧
      Kc * K₁ ^ 4 ≤ x ^ (1 / 10000 : ℝ) ∧ C ≤ x ^ (1 / 10000 : ℝ) ∧
      (16 * (9 * 2 ^ 14 * L)) ^ 4 ≤ x ^ (1 / 5000 : ℝ) ∧ K₁ ^ 4 ≤ x ^ (24 / 25 : ℝ) ∧
      C ^ 2 * T ^ 2 + C ^ 2 * T * G ^ 2 + C ^ 2 * G ^ 2 * T ≤ x ∧
      Real.log x ≤ c / 400 * x ^ (1 / 100 : ℝ) ∧ Real.log x ≤ c / 25600 * x ^ (1 / 27 : ℝ) ∧
      Real.log x ≤ c / 2 * x ^ (1 / 27 : ℝ) ∧ 2 ≤ x ^ (9 / 10 : ℝ) ∧
      (R₀ : ℝ) + 256 ≤ x ^ (1 / 27 : ℝ) ∧ Real.log x ≤ 1 / 2 * x ^ (1 / 27 : ℝ) ∧ T * 64 ≤ x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (Real.exp 1),
      eventually_log_le_mul_rpow s40 one_pos,
      eventually_const_le_rpow s40 (8 * C), eventually_const_le_rpow s40 (16 * (2 ^ 9 * C)),
      eventually_const_le_rpow s40 (2 * (C * (2 ^ 14 * L) ^ 4 * 2 ^ 8 * 8)),
      eventually_const_le_rpow (by norm_num : (0 : ℝ) < 1 / 10000) (Kc * K₁ ^ 4),
      eventually_const_le_rpow (by norm_num : (0 : ℝ) < 1 / 10000) C,
      eventually_const_le_rpow (by norm_num : (0 : ℝ) < 1 / 5000) ((16 * (9 * 2 ^ 14 * L)) ^ 4),
      eventually_const_le_rpow (by norm_num : (0 : ℝ) < 24 / 25) (K₁ ^ 4),
      eventually_ge_atTop (C ^ 2 * T ^ 2 + C ^ 2 * T * G ^ 2 + C ^ 2 * G ^ 2 * T),
      eventually_log_le_mul_rpow (by norm_num : (0 : ℝ) < 1 / 100) (by positivity : 0 < c / 400),
      eventually_log_le_mul_rpow s27 (by positivity : 0 < c / 25600),
      eventually_log_le_mul_rpow s27 (by positivity : 0 < c / 2),
      eventually_const_le_rpow (by norm_num : (0 : ℝ) < 9 / 10) 2,
      eventually_const_le_rpow s27 ((R₀ : ℝ) + 256),
      eventually_log_le_mul_rpow s27 (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop (T * 64)]
      with x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ev
  refine ⟨max x₀ 1, le_max_right _ _, fun x n hxx h1 h2 => ?_⟩
  obtain ⟨x2, xe, lg, c8, c16, c2, cA, cC, c5000, cK, cT, l100, l25600, l2, x910, wR, l12, T64⟩ :=
    hx₀ x ((le_max_left _ _).trans hxx)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  rw [one_mul] at lg
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact xe
  obtain ⟨n1, n2, n3⟩ := scale_bounds hx1 hL h1 h2
  have hn0 : 0 ≤ n := by linarith
  obtain ⟨w1, w2⟩ := boxRadius_bounds hx1
  set w := x ^ (1 / 27 : ℝ) with hw
  have hw256 : 256 ≤ w := by
    have : (0 : ℝ) ≤ R₀ := by positivity
    linarith
  have hNc := translateSiteBound_le hx1 hL n2 n3
  have hNc0 : 0 ≤ translateSiteBound n := by unfold translateSiteBound; positivity
  have hNc1 : 1 ≤ translateSiteBound n := by
    unfold translateSiteBound
    exact one_le_pow₀ (by linarith)
  have hNx : translateSiteBound n ≤ x := by
    calc translateSiteBound n ≤ K₁ ^ 4 * x ^ (1 / 25 : ℝ) := hNc
      _ ≤ x ^ (24 / 25 : ℝ) * x ^ (1 / 25 : ℝ) := by gcongr
      _ = x := by rw [rpow_mul_rpow hx0]; norm_num
  have hC4 : 4 * C ≤ x ^ (1 / 40000 : ℝ) := by linarith
  have hflat0 := boxFlatness_nonneg hx1 hC
  have hflat := two_mul_boxFlatness_le hx1 hC lg hC4
  have htop := boxMeanCurlBound_le_one hx1 hC lg c8
  have hs0 : 0 ≤ boxScale x := by unfold boxScale; positivity
  have htop0 : 0 ≤ boxMeanCurlBound C x := by unfold boxMeanCurlBound; positivity
  have hov : farSiteOverlap T c n ≤ T * x ^ (-100 : ℝ) := by
    unfold farSiteOverlap
    refine mul_le_mul_of_nonneg_left ?_ hT
    have h3 : 100 * Real.log x ≤ c / 4 * n := by
      have : c / 4 * x ^ (1 / 100 : ℝ) ≤ c / 4 * n := mul_le_mul_of_nonneg_left n1 (by positivity)
      linarith
    exact exp_neg_le_rpow hx1 h3
  have hov0 : 0 ≤ farSiteOverlap T c n := by unfold farSiteOverlap; positivity
  have hout : outsideBoxMass T c x ≤ T * x ^ (-100 : ℝ) := by
    unfold outsideBoxMass
    refine mul_le_mul_of_nonneg_left ?_ hT
    have h3 : 100 * Real.log x ≤ c / 4 * ((boxRadius x : ℝ) / 32 - 4) := by
      have h4 : c / 4 * (w / 32 - 4) ≤ c / 4 * ((boxRadius x : ℝ) / 32 - 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h5 : c / 256 * 256 ≤ c / 256 * w := mul_le_mul_of_nonneg_left hw256 (by positivity)
      linarith only [h4, h5, l25600, w1]
    exact exp_neg_le_rpow hx1 h3
  have hout0 : 0 ≤ outsideBoxMass T c x := by unfold outsideBoxMass; positivity
  have hfar := farPairError_le hx1 hC hG hT hNx hNc0 hov hov0 htop htop0 cT
  have hfar0 : 0 ≤ farPairError C G T c n x := by unfold farPairError; positivity
  have hshare := nearPairShare_le hx1 hL n2 n3 c5000
  have hweight := logWeightBound_le hx1 hC lg c16
  have hwt0 : 0 ≤ logWeightBound C x := by unfold logWeightBound; positivity
  have hR1 : (1 : ℝ) ≤ boxRadius x := by linarith
  have hR4 : w ≤ (boxRadius x : ℝ) ^ 4 := by
    have : (boxRadius x : ℝ) ≤ (boxRadius x : ℝ) ^ 4 := le_self_pow₀ hR1 (by norm_num)
    linarith
  have hexp1 : Real.exp (-((boxRadius x : ℝ) ^ 4)) ≤ x⁻¹ / 16 := by
    have h3 : Real.log x + 4 ≤ (boxRadius x : ℝ) ^ 4 := by linarith
    have h4 : Real.exp (-((boxRadius x : ℝ) ^ 4)) ≤ Real.exp (-(Real.log x) + -4) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_add, Real.exp_neg (Real.log x), Real.exp_log hx0] at h4
    have h5 : Real.exp (-4) ≤ 1 / 16 := by
      have h6 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h7 : (16 : ℝ) ≤ Real.exp 4 := by
        have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h6 4
      rw [Real.exp_neg]
      rw [one_div]
      exact inv_anti₀ (by norm_num) h7
    calc Real.exp (-((boxRadius x : ℝ) ^ 4)) ≤ x⁻¹ * Real.exp (-4) := h4
      _ ≤ x⁻¹ * (1 / 16) := by gcongr
      _ = x⁻¹ / 16 := by ring
  have hu0 : 0 < Real.exp (-((boxRadius x : ℝ) ^ 4)) := Real.exp_pos _
  have hxinv : x⁻¹ ≤ x ^ (-(1 / 7) : ℝ) := by
    rw [← Real.rpow_neg_one]; exact rpow_le_rpow_exponent hx1 (by norm_num)
  have hxinv1 : x⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) x2
  have hq7 : x ^ (-(1 / 7) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hexcess : weightExcess C x ≤ x ^ (-(1 / 7) : ℝ) := by
    unfold weightExcess
    linarith
  have hexcess0 : 0 < weightExcess C x := by
    unfold weightExcess
    positivity
  have hrest := marksRemainder_le hx1 hC hc hL hn0 n3 lg c2 (by
    have : c / 2 * w ≤ c / 2 * (boxRadius x : ℝ) := mul_le_mul_of_nonneg_left w1 (by positivity)
    linarith) x910
  have hrest0 : 0 ≤ marksRemainder C c n x := by unfold marksRemainder; positivity
  have hA1 : 1 ≤ formFamilyMass C G n := by
    unfold formFamilyMass
    have : 1 ≤ C ^ 2 * G ^ 4 + C * G ^ 2 + 1 := by
      have : 0 ≤ C ^ 2 * G ^ 4 + C * G ^ 2 := by positivity
      linarith
    exact one_le_mul_of_one_le_of_one_le this hNc1
  have hA2 : formFamilyMass C G n ≤ x ^ (1 / 25 + 1 / 10000 : ℝ) := by
    have e : formFamilyMass C G n = Kc * translateSiteBound n := rfl
    rw [e]
    calc Kc * translateSiteBound n ≤ Kc * (K₁ ^ 4 * x ^ (1 / 25 : ℝ)) := by gcongr
      _ = (Kc * K₁ ^ 4) * x ^ (1 / 25 : ℝ) := by ring
      _ ≤ x ^ (1 / 10000 : ℝ) * x ^ (1 / 25 : ℝ) := by gcongr
      _ = _ := by rw [rpow_mul_rpow hx0]; congr 1; ring
  have hlam : C / x ≤ x ^ (-1 + 1 / 10000 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, Real.rpow_add hx0, mul_comm]
    have : 0 < x ^ (-1 : ℝ) := Real.rpow_pos_of_pos hx0 _
    gcongr
  have hτ : x ^ (-(32 * (2 * Cm + 4)) : ℝ) ≤ 1 / 2 := by
    have : x ^ (-(32 * (2 * Cm + 4)) : ℝ) ≤ x ^ (-1 : ℝ) := rpow_le_rpow_exponent hx1 (by linarith only [hCm])
    rw [Real.rpow_neg_one] at this
    linarith
  have hτ0 : 0 ≤ x ^ (-(32 * (2 * Cm + 4)) : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  refine ⟨⟨div_pos (by linarith) hx0, hlam, hA1, hA2, by positivity, hflat, hfar0, hfar,
    by unfold nearPairShare; positivity, hshare, hexcess0, hexcess, hrest0, hrest.trans (le_refl _),
    (Real.rpow_pos_of_pos hx0 _).le, le_refl _, hτ0, le_refl _⟩, ?_, ?_, hlog1, hτ, ?_, ?_, ?_, ?_⟩
  · have : (R₀ : ℝ) ≤ boxRadius x := by
      have : (0 : ℝ) ≤ 256 := by norm_num
      linarith
    exact_mod_cast this
  · have h3 : 256 ≤ boxRadius x := by
      have : (256 : ℝ) ≤ boxRadius x := by linarith
      exact_mod_cast this
    simp only [averagingRadius]
    omega
  · set t := logWeightBound C x with ht
    set u := Real.exp (-((boxRadius x : ℝ) ^ 4)) with hu
    have t1 : t ≤ 1 / 16 := by linarith
    have u1 : u ≤ 1 / 32 := by linarith
    have e : weightExcess C x = 8 * t + 8 * u := rfl
    rw [e]
    exact (exp_two_mul_le hwt0 t1).trans (one_add_four_mul_le hwt0 t1 hu0 u1)
  · have : Real.exp (-((boxRadius x : ℝ) ^ 4)) ≤ 1 / 32 := by linarith
    linarith
  all_goals
    set φ₀ := boxFlatness C x with hφ₀
    have hq : T * x ^ (-100 : ℝ) * (boxRadius x : ℝ) ^ 6 ≤ 1 := by
      have h3 : (boxRadius x : ℝ) ^ 6 ≤ 64 * x := by
        calc (boxRadius x : ℝ) ^ 6 ≤ (2 * w) ^ 6 := pow_le_pow_left₀ (by positivity) w2 6
          _ = 64 * x ^ (6 / 27 : ℝ) := by rw [mul_pow, hw, rpow_pow_natCast hx0]; norm_num
          _ ≤ 64 * x := by
            have := rpow_le_rpow_exponent hx1 (show (6 / 27 : ℝ) ≤ 1 by norm_num)
            rw [Real.rpow_one] at this
            linarith
      have h4 : 0 < x ^ (-100 : ℝ) := Real.rpow_pos_of_pos hx0 _
      calc T * x ^ (-100 : ℝ) * (boxRadius x : ℝ) ^ 6 ≤ T * x ^ (-100 : ℝ) * (64 * x) := by gcongr
        _ = (T * 64) * x * x ^ (-100 : ℝ) := by ring
        _ ≤ x * x * x ^ (-100 : ℝ) := by gcongr
        _ ≤ 1 := by
          have e : x * x * x ^ (-100 : ℝ) = x ^ (-98 : ℝ) := by
            nth_rewrite 1 [show x = x ^ (1 : ℝ) from (Real.rpow_one x).symm]
            nth_rewrite 2 [show x = x ^ (1 : ℝ) from (Real.rpow_one x).symm]
            rw [rpow_mul_rpow hx0, rpow_mul_rpow hx0]; norm_num
          rw [e]
          exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have hR0 : (0 : ℝ) < boxRadius x := by linarith
    have hRr : (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) * (boxRadius x : ℝ) ≥ 1 := by
      have e : (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) * (boxRadius x : ℝ) = (boxRadius x : ℝ) ^ (1 / 3 : ℝ) := by
        nth_rewrite 2 [show (boxRadius x : ℝ) = (boxRadius x : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
        rw [rpow_mul_rpow hR0]; norm_num
      rw [e]
      exact Real.one_le_rpow hR1 (by norm_num)
    have hRp : 0 < (boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) := Real.rpow_pos_of_pos hR0 _
    have key : outsideBoxMass T c x * boxMeanCurlBound C x ^ 2 ≤ G * φ₀ ^ 2 := by
      have e1 : boxMeanCurlBound C x ^ 2 = (C * boxScale x) ^ 2 * (boxRadius x : ℝ) ^ 4 := by
        simp only [boxMeanCurlBound]; ring
      have e2 : φ₀ ^ 2 = (C * boxScale x) ^ 2 * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 * Real.log x ^ 2 := by
        simp only [hφ₀, boxFlatness]; ring
      rw [e1, e2]
      have h3 : outsideBoxMass T c x * (boxRadius x : ℝ) ^ 4 ≤ ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 := by
        have h4 : outsideBoxMass T c x * (boxRadius x : ℝ) ^ 6 ≤ 1 :=
          (mul_le_mul_of_nonneg_right hout (by positivity)).trans hq
        have h5 : (boxRadius x : ℝ) ^ 2 * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 ≥ 1 := by
          have : 1 ≤ ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ) * (boxRadius x : ℝ)) ^ 2 := one_le_pow₀ hRr
          rw [mul_pow] at this
          linarith only [this]
        have h6 : 0 ≤ outsideBoxMass T c x * (boxRadius x : ℝ) ^ 4 := by positivity
        calc outsideBoxMass T c x * (boxRadius x : ℝ) ^ 4
            ≤ outsideBoxMass T c x * (boxRadius x : ℝ) ^ 4 *
                ((boxRadius x : ℝ) ^ 2 * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2) :=
              le_mul_of_one_le_right h6 h5
          _ = (outsideBoxMass T c x * (boxRadius x : ℝ) ^ 6) * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 := by ring
          _ ≤ 1 * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 := by gcongr
          _ = _ := one_mul _
      have h7 : 1 ≤ G * Real.log x ^ 2 := one_le_mul_of_one_le_of_one_le hG (one_le_pow₀ hlog1)
      calc outsideBoxMass T c x * ((C * boxScale x) ^ 2 * (boxRadius x : ℝ) ^ 4)
          = (C * boxScale x) ^ 2 * (outsideBoxMass T c x * (boxRadius x : ℝ) ^ 4) := by ring
        _ ≤ (C * boxScale x) ^ 2 * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 := by gcongr
        _ ≤ (C * boxScale x) ^ 2 * ((boxRadius x : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 * (G * Real.log x ^ 2) :=
            le_mul_of_one_le_right (by positivity) h7
        _ = _ := by ring
    have hmass : vectorMass C G (translateSiteBound n) (outsideBoxMass T c x) φ₀ (boxMeanCurlBound C x) ≤
        C * G * translateSiteBound n * (2 * (G * φ₀ ^ 2)) := by
      unfold vectorMass
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    have hA : formFamilyMass C G n * (2 * φ₀) ^ 2 =
        (C ^ 2 * G ^ 4 + C * G ^ 2 + 1) * translateSiteBound n * 4 * φ₀ ^ 2 := by
      simp only [formFamilyMass]; ring
    have hφ2 : 0 ≤ translateSiteBound n * φ₀ ^ 2 := by positivity
  · rw [hA]
    calc C * G ^ 2 * vectorMass C G (translateSiteBound n) (outsideBoxMass T c x) φ₀ (boxMeanCurlBound C x)
        ≤ C * G ^ 2 * (C * G * translateSiteBound n * (2 * (G * φ₀ ^ 2))) := by gcongr
      _ = 2 * (C ^ 2 * G ^ 4) * (translateSiteBound n * φ₀ ^ 2) := by ring
      _ ≤ _ := by
        have h9 : 0 ≤ (2 * (C ^ 2 * G ^ 4) + 4 * (C * G ^ 2) + 4) * (translateSiteBound n * φ₀ ^ 2) :=
          mul_nonneg (by positivity) hφ2
        linarith only [h9]
  · rw [hA]
    refine hmass.trans ?_
    have : C * G * translateSiteBound n * (2 * (G * φ₀ ^ 2)) =
        2 * (C * G ^ 2) * (translateSiteBound n * φ₀ ^ 2) := by ring
    rw [this]
    have h9 : 0 ≤ (4 * (C ^ 2 * G ^ 4) + 2 * (C * G ^ 2) + 4) * (translateSiteBound n * φ₀ ^ 2) :=
      mul_nonneg (by positivity) hφ2
    linarith only [h9]
end YangMills.Construction.StateLaws
end
