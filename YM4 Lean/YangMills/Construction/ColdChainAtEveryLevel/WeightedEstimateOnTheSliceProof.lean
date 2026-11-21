import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChainProof
import YangMills.Construction.ColdChainAtEveryLevel.EveryFormSplitsAlongTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.FormNearItsMainPart
import YangMills.Construction.ColdChainAtEveryLevel.SliceNormWithTheRadiusProof
import YangMills.Construction.ColdChainAtEveryLevel.SmoothWeightsThroughTheCurlProof
import YangMills.Construction.ColdChainAtEveryLevel.WeightedEstimateOnTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.WeightsThroughTheAverages
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace WeightedSlice
variable {F : BlockFrame}
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by apply _root_.YangMills.Construction.CoordinateSeminorms.scaleRadius_pos <;> assumption
variable {S : Finset F.Cell}
theorem classWeight_pos (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (l : ℕ) (x : F.Site l) :
    0 < classWeight F φ θ p l x := by apply _root_.YangMills.Construction.NearlyFlatDifferences.classWeight_pos <;> assumption
theorem bondsOver_self (hodd : Odd F.blockSide) (j : ℕ) : bondsOver S S j = innerBonds S j := by apply _root_.YangMills.Construction.BlockAverages.SliceNorm.bondsOver_self <;> assumption
theorem scalar_bound (a A K ε σ τ B N p m v bs cs nO r1 e2 dq1 dq2 csm b₀ Xp Xn M0 Rf : ℝ)
    (hA : 0 < A) (ha : A ^ 2 = a) (hK : 0 < K) (hε0 : 0 ≤ ε) (hε : ε * (K + A * K + 1) ≤ 1 / 16)
    (hσ0 : 0 ≤ σ) (hτ0 : 0 ≤ τ) (hB : 0 ≤ B) (hσ : 36 * (K * (1 + A) * σ) ≤ 1 / 8)
    (hτ : 16 * (τ * K ^ 2) ≤ 1 / 4) (hN0 : 0 ≤ N) (hp0 : 0 ≤ p) (hm0 : 0 ≤ m) (hv0 : 0 ≤ v)
    (hN : N ^ 2 = p ^ 2 + a * m ^ 2 + a * v ^ 2) (hbs0 : 0 ≤ bs) (hcs0 : 0 ≤ cs) (hnO0 : 0 ≤ nO)
    (hr10 : 0 ≤ r1) (he20 : 0 ≤ e2) (hd10 : 0 ≤ dq1) (hd20 : 0 ≤ dq2) (hcsm0 : 0 ≤ csm) (hb00 : 0 ≤ b₀)
    (hnO : nO + bs ≤ K * N) (hcs : cs ≤ nO) (hr1 : r1 ≤ ε * bs) (he2 : e2 ^ 2 ≤ ε ^ 2 * (cs ^ 2 + m ^ 2))
    (hdq : dq1 + dq2 ≤ σ * csm) (hcsm : csm ≤ 2 * (2 * cs + b₀))
    (hM0 : 3 / 4 * p ^ 2 - 2 * p * r1 - p * dq1 + a * m ^ 2 +
      a * (3 / 4 * v ^ 2 - 2 * v * e2 - v * dq2) ≤ M0)
    (hXp : Xp ≤ 2 * p + 2 * r1 + dq1) (hXn : Xn ≤ 2 * v + 2 * e2 + dq2)
    (hb0 : b₀ ≤ K * (Xp + A * m + A * Xn)) (hRf : M0 - τ * nO * b₀ ≤ Rf) (hRB : Rf ≤ B * b₀) :
    nO ≤ 64 * K ^ 2 * B := by
  have hp : p ≤ N := by
    have : p ^ 2 ≤ N ^ 2 := by
      rw [hN]
      have h1 : 0 ≤ a * m ^ 2 := by rw [← ha]; positivity
      have h2 : 0 ≤ a * v ^ 2 := by rw [← ha]; positivity
      linarith
    exact (abs_le_of_sq_le_sq' this hN0).2
  have hm : A * m ≤ N := by
    have : (A * m) ^ 2 ≤ N ^ 2 := by
      rw [hN, mul_pow, ha]
      have h2 : 0 ≤ a * v ^ 2 := by rw [← ha]; positivity
      linarith [sq_nonneg p]
    exact (abs_le_of_sq_le_sq' this hN0).2
  have hv : A * v ≤ N := by
    have : (A * v) ^ 2 ≤ N ^ 2 := by
      rw [hN, mul_pow, ha]
      have h2 : 0 ≤ a * m ^ 2 := by rw [← ha]; positivity
      linarith [sq_nonneg p]
    exact (abs_le_of_sq_le_sq' this hN0).2
  have hbsK : bs ≤ K * N := by linarith
  have hnOK : nO ≤ K * N := by linarith
  have hcsK : cs ≤ K * N := le_trans hcs hnOK
  have hr1K : r1 ≤ ε * (K * N) := le_trans hr1 (mul_le_mul_of_nonneg_left hbsK hε0)
  have he2b : e2 ≤ ε * (cs + m) := by
    have h1 : e2 ^ 2 ≤ (ε * (cs + m)) ^ 2 := by
      refine le_trans he2 ?_
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h2 := mul_nonneg hcs0 hm0
      have e : (cs + m) ^ 2 = cs ^ 2 + m ^ 2 + 2 * (cs * m) := by ring
      rw [e]
      linarith
    exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have hAe : A * e2 ≤ ε * (A * K + 1) * N := by
    have h1 : A * e2 ≤ A * (ε * (cs + m)) := mul_le_mul_of_nonneg_left he2b hA.le
    have h2 : A * cs ≤ A * (K * N) := mul_le_mul_of_nonneg_left hcsK hA.le
    have h3 : ε * (A * cs + A * m) ≤ ε * (A * (K * N) + N) :=
      mul_le_mul_of_nonneg_left (by linarith) hε0
    calc A * e2 ≤ A * (ε * (cs + m)) := h1
      _ = ε * (A * cs + A * m) := by ring
      _ ≤ ε * (A * (K * N) + N) := h3
      _ = _ := by ring
  have hsmall : 2 * r1 + 2 * (A * e2) ≤ N / 8 := by
    have h1 : ε * (K + A * K + 1) * N ≤ 1 / 16 * N := mul_le_mul_of_nonneg_right hε hN0
    have e : ε * (K * N) + ε * (A * K + 1) * N = ε * (K + A * K + 1) * N := by ring
    linarith
  set dq := dq1 + dq2 with hdqd
  have hdA : dq1 + A * dq2 ≤ (1 + A) * dq := by
    rw [hdqd]
    have h1 := mul_nonneg hA.le hd10
    have e : (1 + A) * (dq1 + dq2) = dq1 + dq2 + A * dq1 + A * dq2 := by ring
    rw [e]
    linarith
  have hform : Xp + A * m + A * Xn ≤ 6 * N + (1 + A) * dq := by
    have h1 : A * Xn ≤ A * (2 * v + 2 * e2 + dq2) := mul_le_mul_of_nonneg_left hXn hA.le
    have h2 : A * (2 * v + 2 * e2 + dq2) = 2 * (A * v) + 2 * (A * e2) + A * dq2 := by ring
    linarith
  have hb1 : b₀ ≤ K * (6 * N + (1 + A) * dq) := le_trans hb0 (mul_le_mul_of_nonneg_left hform hK.le)
  have hdq1 : dq ≤ σ * (4 * (K * N) + 2 * b₀) := by
    refine le_trans hdq (mul_le_mul_of_nonneg_left ?_ hσ0)
    linarith
  set κ := K * (1 + A) * σ with hκ
  have hκ1 : κ ≤ 1 / 288 := by linarith
  have hb2 : b₀ ≤ 14 * (K * N) := by
    have h1 : K * (1 + A) * dq ≤ κ * (4 * (K * N) + 2 * b₀) := by
      have := mul_le_mul_of_nonneg_left hdq1 (by positivity : 0 ≤ K * (1 + A))
      refine le_trans this (le_of_eq ?_)
      rw [hκ]
      ring
    have h2 : κ * (4 * (K * N) + 2 * b₀) ≤ 1 / 288 * (4 * (K * N) + 2 * b₀) :=
      mul_le_mul_of_nonneg_right hκ1 (by positivity)
    have h3 : K * (6 * N + (1 + A) * dq) = 6 * (K * N) + K * (1 + A) * dq := by ring
    rw [h3] at hb1
    linarith
  have hdq2 : (1 + A) * dq * N ≤ 1 / 8 * N ^ 2 := by
    have h1 : dq ≤ σ * (32 * (K * N)) := by
      refine le_trans hdq1 (mul_le_mul_of_nonneg_left ?_ hσ0)
      linarith
    have h2 : (1 + A) * dq ≤ 32 * κ * N := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 1 + A)
      refine le_trans this (le_of_eq ?_)
      rw [hκ]
      ring
    have h3 : (1 + A) * dq * N ≤ 32 * κ * N * N := mul_le_mul_of_nonneg_right h2 hN0
    have h4 : 32 * κ * N * N ≤ 1 / 8 * N ^ 2 := by
      have h5 : 32 * κ ≤ 1 / 8 := by linarith
      have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg N)
      have e : 32 * κ * N * N = 32 * κ * N ^ 2 := by ring
      rw [e]
      exact h6
    linarith
  have hM1 : 1 / 2 * N ^ 2 ≤ M0 := by
    have e1 : a * (2 * v * e2) = 2 * (A * v) * (A * e2) := by
      rw [← ha]
      ring
    have e2' : a * (v * dq2) = (A * v) * (A * dq2) := by
      rw [← ha]
      ring
    have h1 : 2 * p * r1 ≤ 2 * N * r1 := mul_le_mul_of_nonneg_right (by linarith) hr10
    have h2 : p * dq1 ≤ N * dq1 := mul_le_mul_of_nonneg_right hp hd10
    have h3 : 2 * (A * v) * (A * e2) ≤ 2 * N * (A * e2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : (A * v) * (A * dq2) ≤ N * (A * dq2) := mul_le_mul_of_nonneg_right hv (by positivity)
    have h5 : 2 * N * r1 + 2 * N * (A * e2) ≤ 1 / 8 * N ^ 2 := by
      have h9 := mul_le_mul_of_nonneg_left hsmall hN0
      have e3 : N * (2 * r1 + 2 * (A * e2)) = 2 * N * r1 + 2 * N * (A * e2) := by ring
      have e4 : N * (N / 8) = 1 / 8 * N ^ 2 := by ring
      rw [e3, e4] at h9
      exact h9
    have h6 : N * dq1 + N * (A * dq2) ≤ (1 + A) * dq * N := by
      have h9 := mul_le_mul_of_nonneg_left hdA hN0
      have e3 : N * (dq1 + A * dq2) = N * dq1 + N * (A * dq2) := by ring
      have e4 : N * ((1 + A) * dq) = (1 + A) * dq * N := by ring
      rw [e3, e4] at h9
      exact h9
    have h7 : 0 ≤ a * m ^ 2 := by rw [← ha]; positivity
    have h8 : a * (3 / 4 * v ^ 2 - 2 * v * e2 - v * dq2) =
        3 / 4 * (a * v ^ 2) - a * (2 * v * e2) - a * (v * dq2) := by ring
    rw [h8, e1, e2'] at hM0
    linarith
  have hR1 : 1 / 4 * N ^ 2 ≤ Rf := by
    have h1 : τ * nO * b₀ ≤ τ * (K * N) * (14 * (K * N)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hnOK hτ0) hb2 hb00 (by positivity)
    have h2 : τ * (K * N) * (14 * (K * N)) = 14 * (τ * K ^ 2) * N ^ 2 := by ring
    have h3 : 14 * (τ * K ^ 2) ≤ 1 / 4 := by
      have : 0 ≤ τ * K ^ 2 := by positivity
      linarith
    have h4 : 14 * (τ * K ^ 2) * N ^ 2 ≤ 1 / 4 * N ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  have hfin : 1 / 4 * N ^ 2 ≤ B * (14 * (K * N)) :=
    le_trans hR1 (le_trans hRB (mul_le_mul_of_nonneg_left hb2 hB))
  have hNle : N ≤ 56 * (K * B) := by
    by_contra hcon
    push Not at hcon
    have hNpos : 0 < N := lt_of_le_of_lt (by positivity) hcon
    have h3 : N * N ≤ 56 * (K * B) * N := by
      have e3 : B * (14 * (K * N)) = 14 * (K * B) * N := by ring
      have e4 : N * N = N ^ 2 := by ring
      rw [e3] at hfin
      rw [e4]
      linarith
    have h2 := le_of_mul_le_mul_right h3 hNpos
    linarith
  calc nO ≤ K * N := hnOK
    _ ≤ K * (56 * (K * B)) := mul_le_mul_of_nonneg_left hNle hK.le
    _ = 56 * K ^ 2 * B := by ring
    _ ≤ 64 * K ^ 2 * B := by
        have h2 : 0 ≤ K ^ 2 * B := by positivity
        linarith
theorem sqrt_sum_sq_add_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (a i + b i) ^ 2) ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) + Real.sqrt (∑ i ∈ s, b i ^ 2) := by apply _root_.YangMills.Construction.CoercivityProof.ellTwo_add <;> assumption
theorem sqrt_sum_sq_mono {ι : Type} (s : Finset ι) (a b : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h : ∀ i ∈ s, a i ≤ b i) :
    Real.sqrt (∑ i ∈ s, a i ^ 2) ≤ Real.sqrt (∑ i ∈ s, b i ^ 2) := by apply _root_.YangMills.Construction.CoercivityProof.ellTwo_mono <;> assumption
theorem sqrt_sum_sq_const_mul {ι : Type} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) (a : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (c * a i) ^ 2) = c * Real.sqrt (∑ i ∈ s, a i ^ 2) := by apply _root_.YangMills.Construction.CoordinateSeminorms.sqrt_sum_mul_sq <;> assumption
theorem weighted_inner_bounds {ι : Type} (s : Finset ι) (d r g : ι → ℍ[ℝ]) (ω W : ι → ℝ)
    (hW : ∀ i ∈ s, 0 < W i) (hω : ∀ i ∈ s, 0 < ω i) (h1 : ∀ i ∈ s, 3 / 4 * W i ^ 2 ≤ ω i ^ 2)
    (h2 : ∀ i ∈ s, ω i ^ 2 ≤ 2 * W i ^ 2) :
    3 / 4 * Real.sqrt (∑ i ∈ s, (W i * ‖d i‖) ^ 2) ^ 2 -
        2 * Real.sqrt (∑ i ∈ s, (W i * ‖d i‖) ^ 2) * Real.sqrt (∑ i ∈ s, ((ω i)⁻¹ * ‖r i‖) ^ 2) -
        Real.sqrt (∑ i ∈ s, (W i * ‖d i‖) ^ 2) * Real.sqrt (∑ i ∈ s, ((W i)⁻¹ * ‖g i‖) ^ 2) ≤
      ∑ i ∈ s, inner ℝ (d i) ((ω i ^ 2) • d i + r i - g i) ∧
    Real.sqrt (∑ i ∈ s, ((W i)⁻¹ * ‖(ω i ^ 2) • d i + r i - g i‖) ^ 2) ≤
      2 * Real.sqrt (∑ i ∈ s, (W i * ‖d i‖) ^ 2) + 2 * Real.sqrt (∑ i ∈ s, ((ω i)⁻¹ * ‖r i‖) ^ 2) +
        Real.sqrt (∑ i ∈ s, ((W i)⁻¹ * ‖g i‖) ^ 2) := by
  have hω2 : ∀ i ∈ s, ω i ≤ 2 * W i := by
    intro i hi
    have h3 := h2 i hi
    have h4 := hW i hi
    have h5 : ω i ^ 2 ≤ (2 * W i) ^ 2 := by nlinarith [sq_nonneg (W i)]
    exact (abs_le_of_sq_le_sq' h5 (by positivity)).2
  set Dd := Real.sqrt (∑ i ∈ s, (W i * ‖d i‖) ^ 2) with hDd
  set Rr := Real.sqrt (∑ i ∈ s, ((ω i)⁻¹ * ‖r i‖) ^ 2) with hRr
  set Gg := Real.sqrt (∑ i ∈ s, ((W i)⁻¹ * ‖g i‖) ^ 2) with hGg
  have hsum0 : 0 ≤ ∑ i ∈ s, (W i * ‖d i‖) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  constructor
  · have e : ∑ i ∈ s, inner ℝ (d i) ((ω i ^ 2) • d i + r i - g i) =
        ∑ i ∈ s, ω i ^ 2 * ‖d i‖ ^ 2 + ∑ i ∈ s, inner ℝ (d i) (r i) - ∑ i ∈ s, inner ℝ (d i) (g i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sub_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [e]
    have hA1 : 3 / 4 * Dd ^ 2 ≤ ∑ i ∈ s, ω i ^ 2 * ‖d i‖ ^ 2 := by
      rw [hDd, Real.sq_sqrt hsum0, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have := mul_le_mul_of_nonneg_right (h1 i hi) (sq_nonneg ‖d i‖)
      calc 3 / 4 * (W i * ‖d i‖) ^ 2 = 3 / 4 * W i ^ 2 * ‖d i‖ ^ 2 := by ring
        _ ≤ _ := this
    have hA2 : -(2 * Dd * Rr) ≤ ∑ i ∈ s, inner ℝ (d i) (r i) := by
      have h3 : ∑ i ∈ s, (ω i * ‖d i‖) * ((ω i)⁻¹ * ‖r i‖) ≤
          Real.sqrt (∑ i ∈ s, (ω i * ‖d i‖) ^ 2) * Rr := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      have h4 : Real.sqrt (∑ i ∈ s, (ω i * ‖d i‖) ^ 2) ≤ 2 * Dd := by
        rw [hDd, ← sqrt_sum_sq_const_mul s 2 (by norm_num)]
        apply sqrt_sum_sq_mono s _ _
        · intro i hi
          have := hω i hi
          positivity
        · intro i hi
          have := mul_le_mul_of_nonneg_right (hω2 i hi) (norm_nonneg (d i))
          linarith
      have h5 : -∑ i ∈ s, (ω i * ‖d i‖) * ((ω i)⁻¹ * ‖r i‖) ≤ ∑ i ∈ s, inner ℝ (d i) (r i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro i hi
        have h6 : (ω i * ‖d i‖) * ((ω i)⁻¹ * ‖r i‖) = ‖d i‖ * ‖r i‖ := by
          have := (hω i hi).ne'
          field_simp
        rw [h6]
        have := abs_real_inner_le_norm (d i) (r i)
        linarith [neg_abs_le (inner ℝ (d i) (r i))]
      have hR0 : 0 ≤ Rr := Real.sqrt_nonneg _
      have h7 : Real.sqrt (∑ i ∈ s, (ω i * ‖d i‖) ^ 2) * Rr ≤ 2 * Dd * Rr :=
        mul_le_mul_of_nonneg_right h4 hR0
      linarith
    have hA3 : ∑ i ∈ s, inner ℝ (d i) (g i) ≤ Dd * Gg := by
      have h3 : ∑ i ∈ s, (W i * ‖d i‖) * ((W i)⁻¹ * ‖g i‖) ≤ Dd * Gg := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      refine le_trans (Finset.sum_le_sum fun i hi => ?_) h3
      have h6 : (W i * ‖d i‖) * ((W i)⁻¹ * ‖g i‖) = ‖d i‖ * ‖g i‖ := by
        have := (hW i hi).ne'
        field_simp
      rw [h6]
      exact real_inner_le_norm _ _
    linarith
  · have h3 : Real.sqrt (∑ i ∈ s, ((W i)⁻¹ * ‖(ω i ^ 2) • d i + r i - g i‖) ^ 2) ≤
        Real.sqrt (∑ i ∈ s, ((2 * (W i * ‖d i‖) + 2 * ((ω i)⁻¹ * ‖r i‖)) + (W i)⁻¹ * ‖g i‖) ^ 2) := by
      apply sqrt_sum_sq_mono s
      · intro i hi
        have := hW i hi
        positivity
      · intro i hi
        have hWi := hW i hi
        have hωi := hω i hi
        have hn : ‖(ω i ^ 2) • d i + r i - g i‖ ≤ ω i ^ 2 * ‖d i‖ + ‖r i‖ + ‖g i‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          have := norm_add_le ((ω i ^ 2) • d i) (r i)
          rw [norm_smul, Real.norm_of_nonneg (by positivity)] at this
          linarith
        have hinv : 0 ≤ (W i)⁻¹ := by positivity
        have h4 := mul_le_mul_of_nonneg_left hn hinv
        refine le_trans h4 ?_
        have e1 : (W i)⁻¹ * (ω i ^ 2 * ‖d i‖ + ‖r i‖ + ‖g i‖) =
            (W i)⁻¹ * ω i ^ 2 * ‖d i‖ + (W i)⁻¹ * ‖r i‖ + (W i)⁻¹ * ‖g i‖ := by ring
        rw [e1]
        have h5 : (W i)⁻¹ * ω i ^ 2 ≤ 2 * W i := by
          rw [inv_mul_le_iff₀ hWi]
          nlinarith [h2 i hi]
        have h6 : (W i)⁻¹ ≤ 2 * (ω i)⁻¹ := by
          rw [inv_le_comm₀ hWi (by positivity)]
          have h7 : (2 * (ω i)⁻¹)⁻¹ = ω i / 2 := by
            field_simp
          rw [h7]
          linarith [hω2 i hi]
        have h8 := mul_le_mul_of_nonneg_right h5 (norm_nonneg (d i))
        have h9 := mul_le_mul_of_nonneg_right h6 (norm_nonneg (r i))
        linarith
    refine le_trans h3 (le_trans (sqrt_sum_sq_add_le _ _ _) ?_)
    have h4 := sqrt_sum_sq_add_le s (fun i => 2 * (W i * ‖d i‖)) (fun i => 2 * ((ω i)⁻¹ * ‖r i‖))
    rw [sqrt_sum_sq_const_mul s 2 (by norm_num), sqrt_sum_sq_const_mul s 2 (by norm_num)] at h4
    linarith
theorem adjointAction_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem linearizedCurl_add (R : F.GaugeField 0) (w u v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (h : ∀ x i, ((w x i : imaginaryQuaternions) : ℍ[ℝ]) = u x i + v x i) (q : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R w q = linearizedCurl R u q + linearizedCurl R v q := by
  simp only [linearizedCurl, h, adjointAction_add]
  abel
theorem parallelAverage_add {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i + g x i) c =
      parallelAverage R f c + parallelAverage R g c := by
  simp only [parallelAverage, adjointAction, mul_add, add_mul, Finset.sum_add_distrib, smul_add]
theorem linearPart_add (R : F.FieldChain) (U₀ U₁ : ChainChart F) (v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hu : ∀ x i, ((U₀.fine x i : imaginaryQuaternions) : ℍ[ℝ]) = U₁.fine x i + v x i)
    (hμ : ∀ j y i, U₀.coarse j y i = U₁.coarse j y i) (j : ℕ) :
    ∀ y k, linearPart R U₀ j y k = linearPart R U₁ j y k + linearPart R (baseOnlyChart v) j y k := by
  induction j with
  | zero =>
    intro y k
    simp only [linearPart, baseOnlyChart]
    exact hu y k
  | succ j ih =>
    intro y k
    simp only [linearPart]
    have h1 : linearPart R U₀ j =
        fun x i => linearPart R U₁ j x i + linearPart R (baseOnlyChart v) j x i := by
      funext x i
      exact ih x i
    rw [h1, parallelAverage_add, hμ]
    simp only [baseOnlyChart]
    by_cases h : j + 1 < F.top
    · simp only [if_pos h, ZeroMemClass.coe_zero]
      abel
    · simp only [if_neg h]
      abel
theorem invertedWeights_classWeight (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) :
    invertedWeights (classWeight F φ θ p) = classWeight F (fun y => -φ y) (-θ) p := by
  funext j x
  simp only [invertedWeights, classWeight, neg_neg]
  have h := scaleRadius_pos hL j p x
  rw [mul_inv, ← Real.exp_neg, Real.rpow_neg (by positivity), inv_inv]
theorem cellwiseL4Norm_le_const_mul (w w' : F.Site 0 → ℝ) (f f' : F.Site 0 → Fin 4 → ℍ[ℝ]) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ x, 0 ≤ w x)
    (h : ∀ b ∈ innerBonds S 0, w b.1 * ‖f b.1 b.2‖ ≤ K * (w' b.1 * ‖f' b.1 b.2‖)) :
    cellwiseL4Norm S w f ≤ K * cellwiseL4Norm S w' f' := by
  classical
  simp only [cellwiseL4Norm]
  have hz : ∀ z ∈ S, Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4) ≤
      K ^ 2 * Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w' b.1 * ‖f' b.1 b.2‖) ^ 4) := by
    intro z _
    have h1 : ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4 ≤
        (K ^ 2) ^ 2 * ∑ b ∈ bondsOver S {z} 0, (w' b.1 * ‖f' b.1 b.2‖) ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      have hb' : b ∈ innerBonds S 0 := by
        simp only [bondsOver, Finset.mem_filter] at hb
        exact hb.1
      have h2 := pow_le_pow_left₀ (mul_nonneg (hw _) (norm_nonneg _)) (h b hb') 4
      refine le_trans h2 (le_of_eq ?_)
      ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h2 := Finset.sum_le_sum hz
  rw [← Finset.mul_sum] at h2
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]
theorem add_pow_four_le (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
theorem cellwiseL4Norm_le_of_le_add (w : F.Site 0 → ℝ) (f g h : F.Site 0 → Fin 4 → ℍ[ℝ]) (hw : ∀ x, 0 ≤ w x)
    (hn : ∀ b ∈ innerBonds S 0, ‖f b.1 b.2‖ ≤ ‖g b.1 b.2‖ + ‖h b.1 b.2‖) :
    cellwiseL4Norm S w f ≤ 2 * (cellwiseL4Norm S w g + cellwiseL4Norm S w h) := by
  classical
  have hz : ∀ z ∈ S, Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4) ≤
      3 * (Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖g b.1 b.2‖) ^ 4) +
        Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖h b.1 b.2‖) ^ 4)) := by
    intro z _
    have hA : 0 ≤ ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖g b.1 b.2‖) ^ 4 :=
      Finset.sum_nonneg fun b _ => by positivity
    have hB : 0 ≤ ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖h b.1 b.2‖) ^ 4 :=
      Finset.sum_nonneg fun b _ => by positivity
    have h1 : ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖f b.1 b.2‖) ^ 4 ≤
        8 * (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖g b.1 b.2‖) ^ 4 +
          ∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖h b.1 b.2‖) ^ 4) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      have hb' : b ∈ innerBonds S 0 := by
        simp only [bondsOver, Finset.mem_filter] at hb
        exact hb.1
      have h2 := mul_le_mul_of_nonneg_left (hn b hb') (hw b.1)
      rw [mul_add] at h2
      have h3 := pow_le_pow_left₀ (mul_nonneg (hw _) (norm_nonneg _)) h2 4
      exact le_trans h3 (add_pow_four_le _ _)
    generalize (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖g b.1 b.2‖) ^ 4) = A at hA h1 ⊢
    generalize (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖h b.1 b.2‖) ^ 4) = B at hB h1 ⊢
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, le_trans h1 ?_⟩
    have h4 := Real.sq_sqrt hA
    have h5 := Real.sq_sqrt hB
    nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg B, mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]
  have hg2 : ∑ z ∈ S, Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖g b.1 b.2‖) ^ 4) =
      cellwiseL4Norm S w g ^ 2 := by
    simp only [cellwiseL4Norm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun y _ => Real.sqrt_nonneg _)]
  have hh2 : ∑ z ∈ S, Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖h b.1 b.2‖) ^ 4) =
      cellwiseL4Norm S w h ^ 2 := by
    simp only [cellwiseL4Norm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun y _ => Real.sqrt_nonneg _)]
  have hsum := Finset.sum_le_sum hz
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hg2, hh2] at hsum
  have hG0 : 0 ≤ cellwiseL4Norm S w g := Real.sqrt_nonneg _
  have hH0 : 0 ≤ cellwiseL4Norm S w h := Real.sqrt_nonneg _
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, le_trans hsum ?_⟩
  nlinarith [mul_nonneg hG0 hH0]
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellwiseL4Norm_le_weightedNorm (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    cellwiseL4Norm S (w 0) (fun x i => U.fine x i) ≤ weightedNorm S R U w := by
  classical
  simp only [cellwiseL4Norm, weightedNorm]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro z hz
  have hnn : 0 ≤ localNormSq S (cellBall S z 3) R U w := by
    simp only [localNormSq]
    have h1 := Real.sqrt_nonneg (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)
    have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
      Finset.sum_nonneg fun q _ => by positivity
    have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
    linarith
  simp only [localNorm]
  rw [Real.sq_sqrt hnn]
  simp only [localNormSq]
  have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun q _ => by positivity
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
  have h4 : Real.sqrt (∑ b ∈ bondsOver S {z} 0,
        (w 0 b.1 * ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖) ^ 4) ≤
      Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton] at hb ⊢
      refine ⟨hb.1, ?_⟩
      rw [hb.2]
      simp only [cellBall, Finset.mem_filter]
      exact ⟨hz, by rw [cellSupDist_self]; omega⟩
    · intro b _ _
      positivity
  linarith
theorem sqrt_sq_add_sq_add_sq_le (x A y z : ℝ) (hx : 0 ≤ x) (hA : 0 ≤ A) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x ^ 2 + A ^ 2 * y ^ 2 + A ^ 2 * z ^ 2) ≤ x + A * y + A * z := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have h1 : 0 ≤ A * y := by positivity
  have h2 : 0 ≤ A * z := by positivity
  nlinarith [mul_nonneg hx h1, mul_nonneg hx h2, mul_nonneg h1 h2]
theorem cellwiseL4Norm_difference_le (S : Finset F.Cell) (R : F.FieldChain) (W Wi : F.SiteWeights)
    (ω : F.Site 0 → ℝ) (U U₂ : ChainChart F) (v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hWp : ∀ (j : ℕ) (x : F.Site j), 0 < W j x) (hWi : ∀ (j : ℕ) (x : F.Site j), Wi j x = (W j x)⁻¹)
    (hω1 : ∀ x ∈ sitesOfCells S 0, 3 / 4 * W 0 x ^ 2 ≤ ω x ^ 2 ∧ ω x ^ 2 ≤ 2 * W 0 x ^ 2)
    (hsplit : ∀ x i, (((chartWeightSq ω W U).fine x i : imaginaryQuaternions) : ℍ[ℝ]) = U₂.fine x i + v x i) :
    cellwiseL4Norm S (Wi 0) (fun x i => v x i) ≤
      2 * (2 * cellwiseL4Norm S (W 0) (fun x i => U.fine x i) + weightedNorm S R U₂ Wi) := by
  classical
  have hcs2 := cellwiseL4Norm_le_weightedNorm (S := S) R U₂ Wi
  have hWi0 : ∀ x, 0 ≤ Wi 0 x := fun x => by
    rw [hWi]
    exact (inv_pos.2 (hWp 0 x)).le
  have h1 := cellwiseL4Norm_le_of_le_add (S := S) (Wi 0) (fun x i => v x i)
    (fun x i => ((chartWeightSq ω W U).fine x i : imaginaryQuaternions)) (fun x i => U₂.fine x i) hWi0 (by
      intro b _
      have e : ((v b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
          ((chartWeightSq ω W U).fine b.1 b.2 : imaginaryQuaternions) - U₂.fine b.1 b.2 := by
        rw [hsplit]
        abel
      change ‖((v b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        ‖(((chartWeightSq ω W U).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ +
        ‖((U₂.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖
      rw [e]
      exact norm_sub_le _ _)
  have h2 := cellwiseL4Norm_le_const_mul (S := S) (Wi 0) (W 0)
    (fun x i => ((chartWeightSq ω W U).fine x i : imaginaryQuaternions))
    (fun x i => U.fine x i) 2 (by norm_num) hWi0 (by
      intro b hb
      have hb1 : b.1 ∈ sitesOfCells S 0 := by
        simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
        exact hb.1.1
      have hw := hWp 0 b.1
      have h3 := (hω1 _ hb1).2
      have e : ‖(((chartWeightSq ω W U).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ =
          ω b.1 ^ 2 * ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ := by
        have e2 : (((chartWeightSq ω W U).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
            (ω b.1 ^ 2) • ((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) := rfl
        rw [e2, norm_smul, Real.norm_of_nonneg (by positivity)]
      change Wi 0 b.1 * ‖(((chartWeightSq ω W U).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        2 * (W 0 b.1 * ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖)
      rw [e, hWi]
      have h4 : (W 0 b.1)⁻¹ * ω b.1 ^ 2 ≤ 2 * W 0 b.1 := by
        rw [inv_mul_le_iff₀ hw]
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg ((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]))
      calc (W 0 b.1)⁻¹ * (ω b.1 ^ 2 * ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖)
          = (W 0 b.1)⁻¹ * ω b.1 ^ 2 * ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ := by ring
        _ ≤ 2 * W 0 b.1 * ‖((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ := h5
        _ = _ := by ring)
  linarith
set_option maxHeartbeats 2000000 in
theorem weighted_estimate_of_bounds (a A K ε σ τ B : ℝ) (hA : 0 < A) (ha : A ^ 2 = a) (hK : 0 < K)
    (hε0 : 0 ≤ ε) (hε : ε * (K + A * K + 1) ≤ 1 / 16) (hσ0 : 0 ≤ σ) (hτ0 : 0 ≤ τ) (hB : 0 ≤ B)
    (hσ : 36 * (K * (1 + A) * σ) ≤ 1 / 8) (hτ : 16 * (τ * K ^ 2) ≤ 1 / 4) (hodd : Odd F.blockSide)
    (S : Finset F.Cell) (R : F.FieldChain) (W Wi : F.SiteWeights) (bw : F.Site 0 → ℝ) (ω : F.Site 0 → ℝ)
    (U U₂ : ChainChart F) (v : F.Site 0 → Fin 4 → imaginaryQuaternions) (Rf : ℝ)
    (hWp : ∀ (j : ℕ) (x : F.Site j), 0 < W j x) (hWi : ∀ (j : ℕ) (x : F.Site j), Wi j x = (W j x)⁻¹)
    (hωp : ∀ x, 0 < ω x)
    (hω1 : ∀ x ∈ sitesOfCells S 0, 3 / 4 * W 0 x ^ 2 ≤ ω x ^ 2 ∧ ω x ^ 2 ≤ 2 * W 0 x ^ 2)
    (hsplit : ∀ x i, (((chartWeightSq ω W U).fine x i : imaginaryQuaternions) : ℍ[ℝ]) = U₂.fine x i + v x i)
    (hmu : ∀ j y i, U₂.coarse j y i = (chartWeightSq ω W U).coarse j y i)
    (hSN1 : weightedNorm S R U W + weightedBondL2Norm S bw (fun x i => U.fine x i) ≤
      K * Real.sqrt (quadraticFormNormSq a S R U W))
    (hSN2 : weightedNorm S R U₂ Wi ≤ K * Real.sqrt (quadraticFormNormSq a S R U₂ Wi))
    (hC : ∑ q ∈ plaquettesOver S S 0, ((ω q.1)⁻¹ *
        ‖linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
          (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q‖) ^ 2 ≤
      ε ^ 2 * weightedBondL2Norm S bw (fun x i => U.fine x i) ^ 2)
    (hAv : ∑ c ∈ innerBonds S F.top, ((W F.top c.1)⁻¹ * ‖linearPart R (chartWeightSq ω W U) F.top c.1 c.2 -
        (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2‖) ^ 2 ≤
      ε ^ 2 * (cellwiseL4Norm S (W 0) (fun x i => U.fine x i) ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1), (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2))
    (hFlat : Real.sqrt (∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2) +
        Real.sqrt (∑ c ∈ innerBonds S F.top, (Wi F.top c.1 * ‖linearPart R (baseOnlyChart v) F.top c.1 c.2‖) ^ 2) ≤
      σ * cellwiseL4Norm S (Wi 0) (fun x i => v x i))
    (hForm : principalHessian a S R U U₂ - τ * weightedNorm S R U W * weightedNorm S R U₂ Wi ≤ Rf)
    (hRB : Rf ≤ B * weightedNorm S R U₂ Wi) :
    weightedNorm S R U W ≤ 64 * K ^ 2 * B := by
  classical
  have ha0 : 0 < a := by rw [← ha]; positivity
  have hbnd : bondsOver S S F.top = innerBonds S F.top := bondsOver_self hodd F.top
  have hbndj : ∀ j, bondsOver S S (j + 1) = innerBonds S (j + 1) := fun j => bondsOver_self hodd (j + 1)
  have hq1 : ∀ q ∈ plaquettesOver S S 0, q.1 ∈ sitesOfCells S 0 := by
    intro q hq
    simp only [plaquettesOver, innerPlaquettes, Finset.mem_filter, Finset.mem_product] at hq
    exact hq.1.1.1
  have hcurl : ∀ q, linearizedCurl (R 0) U₂.fine q =
      (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q +
        (linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
          (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q) -
        linearizedCurl (R 0) v q := by
    intro q
    have h := linearizedCurl_add (R 0) (chartWeightSq ω W U).fine U₂.fine v hsplit q
    have e : (fun x i => (ω x ^ 2) • U.fine x i) = (chartWeightSq ω W U).fine := rfl
    rw [e, h]
    abel
  obtain ⟨hT1, hX1⟩ := weighted_inner_bounds (plaquettesOver S S 0) (fun q => linearizedCurl (R 0) U.fine q)
    (fun q => linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
      (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q)
    (fun q => linearizedCurl (R 0) v q) (fun q => ω q.1) (fun q => W 0 q.1)
    (fun q _ => hWp _ _) (fun q _ => hωp _) (fun q hq => (hω1 _ (hq1 q hq)).1)
    (fun q hq => (hω1 _ (hq1 q hq)).2)
  have hlf : ∀ c : F.Site F.top × Fin 4, linearPart R U₂ F.top c.1 c.2 =
      (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2 +
        (linearPart R (chartWeightSq ω W U) F.top c.1 c.2 - (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2) -
        linearPart R (baseOnlyChart v) F.top c.1 c.2 := by
    intro c
    have h := linearPart_add R (chartWeightSq ω W U) U₂ v hsplit (fun j y i => (hmu j y i).symm) F.top c.1 c.2
    rw [h]
    abel
  obtain ⟨hT3, hX3⟩ := weighted_inner_bounds (bondsOver S S F.top) (fun c => linearPart R U F.top c.1 c.2)
    (fun c => linearPart R (chartWeightSq ω W U) F.top c.1 c.2 - (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2)
    (fun c => linearPart R (baseOnlyChart v) F.top c.1 c.2) (fun c => W F.top c.1) (fun c => W F.top c.1)
    (fun c _ => hWp _ _) (fun c _ => hWp _ _)
    (fun c _ => by nlinarith [sq_nonneg (W F.top c.1)]) (fun c _ => by nlinarith [sq_nonneg (W F.top c.1)])
  have eT1 : ∑ q ∈ plaquettesOver S S 0, inner ℝ (linearizedCurl (R 0) U.fine q)
      ((ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q +
        (linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
          (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q) -
        linearizedCurl (R 0) v q) =
      ∑ q ∈ plaquettesOver S S 0, inner ℝ (linearizedCurl (R 0) U.fine q) (linearizedCurl (R 0) U₂.fine q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [← hcurl]
  have eX1 : ∑ q ∈ plaquettesOver S S 0, ((W 0 q.1)⁻¹ * ‖(ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q +
        (linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
          (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q) -
        linearizedCurl (R 0) v q‖) ^ 2 =
      ∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) U₂.fine q‖) ^ 2 := by
    apply Finset.sum_congr rfl
    intro q _
    rw [← hcurl, hWi]
  have eG1 : ∑ q ∈ plaquettesOver S S 0, ((W 0 q.1)⁻¹ * ‖linearizedCurl (R 0) v q‖) ^ 2 =
      ∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2 := by
    apply Finset.sum_congr rfl
    intro q _
    rw [hWi]
  rw [eT1, eG1] at hT1
  rw [eX1, eG1] at hX1
  have eT3 : ∑ c ∈ bondsOver S S F.top, inner ℝ (linearPart R U F.top c.1 c.2)
      ((W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2 +
        (linearPart R (chartWeightSq ω W U) F.top c.1 c.2 - (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2) -
        linearPart R (baseOnlyChart v) F.top c.1 c.2) =
      ∑ c ∈ bondsOver S S F.top, inner ℝ (linearPart R U F.top c.1 c.2) (linearPart R U₂ F.top c.1 c.2) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [← hlf]
  have eX3 : ∑ c ∈ bondsOver S S F.top, ((W F.top c.1)⁻¹ * ‖(W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2 +
        (linearPart R (chartWeightSq ω W U) F.top c.1 c.2 - (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2) -
        linearPart R (baseOnlyChart v) F.top c.1 c.2‖) ^ 2 =
      ∑ c ∈ bondsOver S S F.top, (Wi F.top c.1 * ‖linearPart R U₂ F.top c.1 c.2‖) ^ 2 := by
    apply Finset.sum_congr rfl
    intro c _
    rw [← hlf, hWi]
  have eG3 : ∑ c ∈ bondsOver S S F.top, ((W F.top c.1)⁻¹ * ‖linearPart R (baseOnlyChart v) F.top c.1 c.2‖) ^ 2 =
      ∑ c ∈ innerBonds S F.top, (Wi F.top c.1 * ‖linearPart R (baseOnlyChart v) F.top c.1 c.2‖) ^ 2 := by
    rw [hbnd]
    apply Finset.sum_congr rfl
    intro c _
    rw [hWi]
  rw [eT3, eG3] at hT3
  rw [eX3, eG3] at hX3
  have hmuE : ∀ j y i, ((U₂.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) =
      (W (j + 1) y ^ 2) • ((U.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro j y i
    rw [hmu]
    rfl
  have eT2 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      inner ℝ ((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])
        ((U₂.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    rw [hmuE, inner_smul_right, real_inner_self_eq_norm_sq, mul_pow]
    rfl
  have eM2 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      (Wi (j + 1) c.1 * ‖U₂.coarse j c.1 c.2‖) ^ 2 =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    have hw := hWp (j + 1) c.1
    have e1 : ‖U₂.coarse j c.1 c.2‖ = W (j + 1) c.1 ^ 2 * ‖U.coarse j c.1 c.2‖ := by
      change ‖((U₂.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ = _
      rw [hmuE, norm_smul, Real.norm_of_nonneg (by positivity)]
      rfl
    rw [e1, hWi]
    congr 1
    field_simp
  have hP0 : 0 ≤ ∑ q ∈ plaquettesOver S S 0, (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 :=
    Finset.sum_nonneg fun q _ => by positivity
  have hMm0 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
  have hNu0 : 0 ≤ ∑ c ∈ bondsOver S S F.top, (W F.top c.1 * ‖linearPart R U F.top c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun c _ => by positivity
  have hform1 : quadraticFormNormSq a S R U W =
      (∑ q ∈ plaquettesOver S S 0, (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2) +
      a * (∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
        (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2) +
      a * (∑ c ∈ bondsOver S S F.top, (W F.top c.1 * ‖linearPart R U F.top c.1 c.2‖) ^ 2) := rfl
  have hform2 : quadraticFormNormSq a S R U₂ Wi =
      (∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) U₂.fine q‖) ^ 2) +
      a * (∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
        (Wi (j + 1) c.1 * ‖U₂.coarse j c.1 c.2‖) ^ 2) +
      a * (∑ c ∈ bondsOver S S F.top, (Wi F.top c.1 * ‖linearPart R U₂ F.top c.1 c.2‖) ^ 2) := rfl
  have hmain : principalHessian a S R U U₂ =
      (∑ q ∈ plaquettesOver S S 0, inner ℝ (linearizedCurl (R 0) U.fine q) (linearizedCurl (R 0) U₂.fine q)) +
      a * (∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
        inner ℝ ((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])
          ((U₂.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])) +
      a * (∑ c ∈ bondsOver S S F.top,
        inner ℝ (linearPart R U F.top c.1 c.2) (linearPart R U₂ F.top c.1 c.2)) := rfl
  rw [eM2] at hform2
  rw [eT2] at hmain
  have hcs := cellwiseL4Norm_le_weightedNorm (S := S) R U W
  have hcsm := cellwiseL4Norm_difference_le S R W Wi ω U U₂ v hWp hWi hω1 hsplit
  generalize hpd : (∑ q ∈ plaquettesOver S S 0, (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2) = P
    at hT1 hX1 hP0 hform1
  generalize hmd : (∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2) = Mm at hMm0 hform1 hform2 hmain
  generalize hnd : (∑ c ∈ bondsOver S S F.top, (W F.top c.1 * ‖linearPart R U F.top c.1 c.2‖) ^ 2) = Nu
    at hT3 hX3 hNu0 hform1
  have hform0 : 0 ≤ quadraticFormNormSq a S R U W := by
    rw [hform1]
    positivity
  have hN2 : Real.sqrt (quadraticFormNormSq a S R U W) ^ 2 =
      Real.sqrt P ^ 2 + a * Real.sqrt Mm ^ 2 + a * Real.sqrt Nu ^ 2 := by
    rw [Real.sq_sqrt hform0, Real.sq_sqrt hP0, Real.sq_sqrt hMm0, Real.sq_sqrt hNu0]
    exact hform1
  have hr1 : Real.sqrt (∑ q ∈ plaquettesOver S S 0, ((ω q.1)⁻¹ *
      ‖linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
        (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q‖) ^ 2) ≤
      ε * weightedBondL2Norm S bw (fun x i => U.fine x i) := by
    apply Real.sqrt_le_iff.2
    have hbs0 : 0 ≤ weightedBondL2Norm S bw (fun x i => U.fine x i) := Real.sqrt_nonneg _
    refine ⟨by positivity, le_trans hC (le_of_eq ?_)⟩
    ring
  have he2 : Real.sqrt (∑ c ∈ bondsOver S S F.top, ((W F.top c.1)⁻¹ *
      ‖linearPart R (chartWeightSq ω W U) F.top c.1 c.2 -
        (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2‖) ^ 2) ^ 2 ≤
      ε ^ 2 * (cellwiseL4Norm S (W 0) (fun x i => U.fine x i) ^ 2 + Real.sqrt Mm ^ 2) := by
    rw [Real.sq_sqrt (Finset.sum_nonneg fun c _ => by positivity), hbnd, Real.sq_sqrt hMm0, ← hmd]
    simp only [hbndj]
    exact hAv
  have hb₀ : weightedNorm S R U₂ Wi ≤
      K * (Real.sqrt (∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) U₂.fine q‖) ^ 2) +
      A * Real.sqrt Mm +
      A * Real.sqrt (∑ c ∈ bondsOver S S F.top, (Wi F.top c.1 * ‖linearPart R U₂ F.top c.1 c.2‖) ^ 2)) := by
    refine le_trans hSN2 (mul_le_mul_of_nonneg_left ?_ hK.le)
    have hs1 : 0 ≤ ∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) U₂.fine q‖) ^ 2 :=
      Finset.sum_nonneg fun q _ => by positivity
    have hs3 : 0 ≤ ∑ c ∈ bondsOver S S F.top, (Wi F.top c.1 * ‖linearPart R U₂ F.top c.1 c.2‖) ^ 2 :=
      Finset.sum_nonneg fun c _ => by positivity
    have h := sqrt_sq_add_sq_add_sq_le _ A _ _
      (Real.sqrt_nonneg (∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) U₂.fine q‖) ^ 2))
      hA.le (Real.sqrt_nonneg Mm)
      (Real.sqrt_nonneg (∑ c ∈ bondsOver S S F.top, (Wi F.top c.1 * ‖linearPart R U₂ F.top c.1 c.2‖) ^ 2))
    rw [Real.sq_sqrt hs1, Real.sq_sqrt hMm0, Real.sq_sqrt hs3, ha, ← hform2] at h
    exact h
  have hM0 : 3 / 4 * Real.sqrt P ^ 2 -
      2 * Real.sqrt P * Real.sqrt (∑ q ∈ plaquettesOver S S 0, ((ω q.1)⁻¹ *
        ‖linearizedCurl (R 0) (fun x i => (ω x ^ 2) • U.fine x i) q -
          (ω q.1 ^ 2) • linearizedCurl (R 0) U.fine q‖) ^ 2) -
      Real.sqrt P * Real.sqrt (∑ q ∈ plaquettesOver S S 0, (Wi 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2) +
      a * Real.sqrt Mm ^ 2 + a * (3 / 4 * Real.sqrt Nu ^ 2 -
        2 * Real.sqrt Nu * Real.sqrt (∑ c ∈ bondsOver S S F.top, ((W F.top c.1)⁻¹ *
          ‖linearPart R (chartWeightSq ω W U) F.top c.1 c.2 -
            (W F.top c.1 ^ 2) • linearPart R U F.top c.1 c.2‖) ^ 2) -
        Real.sqrt Nu * Real.sqrt (∑ c ∈ innerBonds S F.top,
          (Wi F.top c.1 * ‖linearPart R (baseOnlyChart v) F.top c.1 c.2‖) ^ 2)) ≤
      principalHessian a S R U U₂ := by
    rw [hmain, Real.sq_sqrt hMm0]
    have h3 := mul_le_mul_of_nonneg_left hT3 ha0.le
    linarith
  exact scalar_bound a A K ε σ τ B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA ha hK hε0 hε hσ0 hτ0 hB hσ hτ
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hN2
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hSN1 hcs hr1 he2 hFlat hcsm hM0 hX1 hX3 hb₀ hForm hRB
theorem exp_le_one_add_two_mul (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : Real.exp u ≤ 1 + 2 * u := by apply _root_.YangMills.Construction.BlockAverages.SmoothWeightCurl.exp_le_one_add_two_mul <;> assumption
theorem sq_bounds_of_exp_bounds (w x del : ℝ) (hw : 0 < w) (hd0 : 0 ≤ del) (hd : del ≤ 1 / 8)
    (h1 : Real.exp (-del) * w ≤ x) (h2 : x ≤ Real.exp del * w) :
    3 / 4 * w ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 2 * w ^ 2 := by
  have h3 : 7 / 8 ≤ Real.exp (-del) := by
    have := Real.add_one_le_exp (-del)
    linarith
  have h4 : Real.exp del ≤ 5 / 4 := by
    have := exp_le_one_add_two_mul del hd0 (by linarith)
    linarith
  have h5 : 7 / 8 * w ≤ x := le_trans (mul_le_mul_of_nonneg_right h3 hw.le) h1
  have h6 : x ≤ 5 / 4 * w := le_trans h2 (mul_le_mul_of_nonneg_right h4 hw.le)
  constructor
  · have := pow_le_pow_left₀ (by positivity) h5 2
    nlinarith [sq_nonneg w]
  · have h7 : 0 ≤ x := le_trans (by positivity) h5
    have := pow_le_pow_left₀ h7 h6 2
    nlinarith [sq_nonneg w]
end WeightedSlice
open WeightedSlice in
theorem weightedSliceEstimate (hSN : sliceNormRadiusBoundStatement)
    (hSp : sliceDecompositionStatement) (hCu : smoothWeightCurlCommutatorStatement)
    (hAv : weightAverageCommutatorStatement) (hFo : hessianNearPrincipalStatement)
    (hFl : covariantDiffNearlyFlatStatement) : weightedSliceEstimateStatement := by
  intro a ha
  obtain ⟨c₁, K, L₁, hc₁, hK, hSN⟩ := hSN a ha
  have hA : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hA2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  generalize Real.sqrt a = A at hA hA2
  have hε0 : 0 < 1 / (16 * (K + A * K + 1)) := by positivity
  have hε : 1 / (16 * (K + A * K + 1)) * (K + A * K + 1) ≤ 1 / 16 := by
    apply le_of_eq
    field_simp
  generalize 1 / (16 * (K + A * K + 1)) = ε at hε0 hε
  obtain ⟨θ₁, del₁, hθ₁, hθ₁8, hd₁, hd₁8, hCu⟩ := hCu ε hε0
  obtain ⟨θ₂, del₂, hθ₂, hθ₂8, hd₂, hd₂8, hAv⟩ := hAv ε hε0
  have hθ0 : 0 < min θ₁ θ₂ := lt_min hθ₁ hθ₂
  have hθ8 : min θ₁ θ₂ ≤ 1 / 8 := le_trans (min_le_left _ _) hθ₁8
  have hd0 : 0 < min del₁ del₂ := lt_min hd₁ hd₂
  have hd8 : min del₁ del₂ ≤ 1 / 8 := le_trans (min_le_left _ _) hd₁8
  refine ⟨min θ₁ θ₂, min del₁ del₂, 64 * K ^ 2, hθ0, hθ8, hd0, hd8, by positivity, ?_⟩
  obtain ⟨L₃, hFo⟩ := hFo a (min θ₁ θ₂) (min del₁ del₂) ha hθ0.le hθ8 hd0 hd8
  obtain ⟨L₂, hFl⟩ := hFl
  obtain ⟨c₄, L₄, hc₄, hSp⟩ := hSp
  refine ⟨max (max L₁ L₂) (max (max L₃ L₄) 5), ?_⟩
  intro L hoddL hLL
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL3 : L₃ ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL4 : L₄ ≤ L := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have h5L : 5 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL
  obtain ⟨c₃, C₃, hc₃, hC₃, hFo⟩ := hFo L hoddL hL3
  obtain ⟨c₂, C₂, hc₂, hC₂, hFl⟩ := hFl L hoddL hL2
  have hs1 : 0 < 1 / (288 * (K * (1 + A) * C₂)) := by positivity
  have hs2 : 0 < 1 / (64 * (C₃ * K ^ 2)) := by positivity
  refine ⟨min (min (min c₁ c₂) (min c₃ c₄)) (min (1 / (288 * (K * (1 + A) * C₂))) (1 / (64 * (C₃ * K ^ 2)))),
    lt_min (lt_min (lt_min hc₁ hc₂) (lt_min hc₃ hc₄)) (lt_min hs1 hs2), ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold φ p θ' hθ' hφ U f B hB0 hU hfeq hfB
  subst hFL
  have hodd := hoddL
  have h5 := h5L
  have hL := hodd.pos
  have hsc1 : s ≤ c₁ := le_trans hsc (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hsc2 : s ≤ c₂ := le_trans hsc (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hsc3 : s ≤ c₃ := le_trans hsc (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hsc4 : s ≤ c₄ := le_trans hsc (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hsc5 : s ≤ 1 / (288 * (K * (1 + A) * C₂)) := le_trans hsc (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsc6 : s ≤ 1 / (64 * (C₃ * K ^ 2)) := le_trans hsc (le_trans (min_le_right _ _) (min_le_right _ _))
  generalize hdd : min del₁ del₂ = del at *
  generalize hθd : min θ₁ θ₂ = θ at *
  have hdel1 : del ≤ del₁ := by rw [← hdd]; exact min_le_left _ _
  have hdel2 : del ≤ del₂ := by rw [← hdd]; exact min_le_right _ _
  have hθ1 : θ ≤ θ₁ := by rw [← hθd]; exact min_le_left _ _
  have hθ2 : θ ≤ θ₂ := by rw [← hθd]; exact min_le_right _ _
  have hθabs : |θ'| ≤ θ := by
    rcases hθ' with rfl | rfl | rfl
    · rw [abs_of_pos hθ0]
    · simpa using hθ0.le
    · rw [abs_neg, abs_of_pos hθ0]
  have hdabs : |del| ≤ 1 / 8 := by rw [abs_of_pos hd0]; exact hd8
  have hθabs8 : |θ'| ≤ 1 / 8 := le_trans hθabs hθ8
  have hφa : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y' := by
    intro y y'
    rw [abs_of_pos hd0]
    exact hφ y y'
  have hφn : ∀ y y', |(fun y => -φ y) y - (fun y => -φ y) y'| ≤ |del| * cellSupDist y y' := by
    intro y y'
    have e : (fun y => -φ y) y - (fun y => -φ y) y' = -(φ y - φ y') := by
      simp only []
      ring
    rw [e, abs_neg]
    exact hφa y y'
  have hθn : |(-θ')| ≤ 1 / 8 := by rwa [abs_neg]
  obtain ⟨ω, hωp, hωc, hωcurl⟩ := hCu F S (referenceFieldChain S V 0) hodd h5 φ θ' del p
    (le_trans hθabs hθ1) hd0.le hdel1 hφ
  have hWp : ∀ (j : ℕ) (x : F.Site j), 0 < classWeight F φ θ' p j x := classWeight_pos hL φ θ' p
  obtain ⟨u₁, ξ, hin, hmf, hre, heq⟩ := hSp F m S hodd hL4 hamb hm hreg s V hs hsc4 hcold
    (chartWeightSq ω (classWeight F φ θ' p) U).fine
  set v : F.Site 0 → Fin 4 → imaginaryQuaternions :=
    fun x i => (chartWeightSq ω (classWeight F φ θ' p) U).fine x i - u₁ x i with hv
  have hvD : ∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) =
      covariantDiff (referenceFieldChain S V 0) ξ x i := by
    intro x i
    simp only [hv, Submodule.coe_sub]
    rw [heq]
    abel
  set U₂ : ChainChart F := ⟨u₁, (chartWeightSq ω (classWeight F φ θ' p) U).coarse⟩ with hU₂
  have hsplit : ∀ x i, (((chartWeightSq ω (classWeight F φ θ' p) U).fine x i : imaginaryQuaternions) : ℍ[ℝ]) =
      U₂.fine x i + v x i := by
    intro x i
    simp only [hv, hU₂, Submodule.coe_sub]
    abel
  have hσ : 36 * (K * (1 + A) * (C₂ * s)) ≤ 1 / 8 := by
    have h1 : s * (288 * (K * (1 + A) * C₂)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hsc5
      exact hsc5
    nlinarith
  have hτ : 16 * (C₃ * s * K ^ 2) ≤ 1 / 4 := by
    have h1 : s * (64 * (C₃ * K ^ 2)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hsc6
      exact hsc6
    nlinarith
  have hInv := invertedWeights_classWeight hL φ θ' p
  have hSN2 := hSN F m S hodd hL1 hamb hm hreg s V hs hsc1 hcold (fun y => -φ y) (-θ') del p hθn hdabs hφn U₂ hin
  rw [← hInv] at hSN2
  have hbs2 : 0 ≤ weightedBondL2Norm S (fun x => invertedWeights (classWeight F φ θ' p) 0 x / scaleRadius F 0 p x)
      (fun x i => U₂.fine x i) := Real.sqrt_nonneg _
  have hFl2 := hFl F m S rfl hamb hm hreg s V hs hsc2 hcold (fun y => -φ y) (-θ') del p hθn hdabs hφn ξ v hmf hvD
  rw [← hInv] at hFl2
  have hFo2 := hFo F m S rfl hamb hm hreg s V hs hsc3 hcold φ θ' p hθ' hφ U U₂
  refine weighted_estimate_of_bounds a A K ε (C₂ * s) (C₃ * s) B hA hA2 hK hε0.le hε (by positivity)
    (by positivity) hB0 hσ hτ
    hodd S (referenceFieldChain S V) (classWeight F φ θ' p) (invertedWeights (classWeight F φ θ' p))
    (fun x => classWeight F φ θ' p 0 x / scaleRadius F 0 p x) ω U U₂ v
    (referenceSecondDeriv a S (referenceFieldChain S V) V U U₂) hWp (fun _ _ => rfl) hωp
    (fun x hx => sq_bounds_of_exp_bounds _ _ del (hWp 0 x) hd0.le hd8 (hωc x hx).1 (hωc x hx).2)
    hsplit (fun _ _ _ => rfl)
    (hSN F m S hodd hL1 hamb hm hreg s V hs hsc1 hcold φ θ' del p hθabs8 hdabs hφa U hU)
    (by linarith) (hωcurl U.fine) ?_ ?_ ?_ ?_
  · exact hAv F S (referenceFieldChain S V) hodd h5 φ θ' p ω (le_trans hθabs hθ2)
      (fun y y' => le_trans (hφ y y') (mul_le_mul_of_nonneg_right hdel2 (Nat.cast_nonneg _)))
      (fun x hx => ⟨le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (hWp 0 x).le)
          (hωc x hx).1,
        le_trans (hωc x hx).2 (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hdel2) (hWp 0 x).le)⟩) U
  · exact hFl2
  · have h1 := (abs_le.1 hFo2).1
    linarith
  · rw [hfeq U₂ hin]
    exact le_trans (le_abs_self _) (hfB U₂ hin)
end YangMills.Construction.BlockAverages
end
