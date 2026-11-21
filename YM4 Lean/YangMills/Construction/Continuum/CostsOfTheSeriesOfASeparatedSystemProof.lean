import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecay
import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystem
import YangMills.Construction.Continuum.CostsOfTheSeriesOfASeparatedSystem
import YangMills.Construction.Continuum.SumOverTheFrequenciesOfASystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
open SmoothMaps
private lemma mul_le_mul_zpow_of_decay_of_growth {n : ℕ} {w u v K B : ℝ} (hw : 0 < w) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hdec : w ^ (5 * n + 1) * u ≤ K) (hgrow : v ≤ B * w ^ n) :
    u * v ≤ K * B * w ^ (-(4 * (n : ℤ)) - 1) := by
  have hwn : 0 < w ^ n := pow_pos hw n
  have hwpow : 0 < w ^ (4 * n + 1) := pow_pos hw _
  have hB : 0 ≤ B := by
    by_contra hB'
    have : B * w ^ n < 0 := mul_neg_of_neg_of_pos (not_le.mp hB') hwn
    linarith
  have hexp : (-(4 * (n : ℤ)) - 1) = -((4 * n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have hsplit : w ^ (5 * n + 1) = w ^ (4 * n + 1) * w ^ n := by
    rw [← pow_add]
    congr 1
    ring
  rw [hexp, zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hwpow]
  calc u * v * w ^ (4 * n + 1) ≤ u * (B * w ^ n) * w ^ (4 * n + 1) := by
        gcongr
    _ = (w ^ (5 * n + 1) * u) * B := by
        rw [hsplit]
        ring
    _ ≤ K * B := mul_le_mul_of_nonneg_right hdec hB
theorem separatedSystemCostsSummable_holds
    (hDec : SystemCoeffsDecay)
    (hMode : ModeCostOfSeparated)
    (hFreq : FrequencySum.FrequencySumBound) :
    SeparatedSystemCostsSummable := by
  intro n hn Q hQ Φ hΦ c a G T hT
  have hn1 : 1 ≤ n := by omega
  have hd := hDec n hn1 Q Φ hΦ (5 * n + 1)
  have hc := hMode n hn Q hQ c a G T hT
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (2 * modeConst) ^ n * max 1 c ^ n * Q.scale ^ (-(n : ℤ)) * G *
      Q.sepWeight a := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 ^ (5 * n + 1) * scaledSupNorm (5 * n + 1) Q.scale Φ := ⟨_, rfl⟩
  let g : Q.freqLattice → ℝ := fun ξ =>
    ‖Q.fourierCoeff Φ ξ‖ * ‖complexifyAtModes T Q ξ‖
  have hg : ∀ ξ : Q.freqLattice, ‖g ξ‖ = g ξ := fun ξ =>
    Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hle : ∀ ξ : Q.freqLattice,
      ‖g ξ‖ ≤ (K * B) * (1 + Q.scale * coordSupNorm (ξ : Config n)) ^ (-(4 * (n : ℤ)) - 1) := by
    intro ξ
    have hnorm : 0 ≤ coordSupNorm (ξ : Config n) :=
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
    have hpos : 0 < 1 + Q.scale * coordSupNorm (ξ : Config n) := by
      have := mul_nonneg Q.scale_pos.le hnorm
      linarith
    rw [hg]
    refine mul_le_mul_zpow_of_decay_of_growth hpos (norm_nonneg _) (norm_nonneg _) ?_ ?_
    · rw [hK]
      exact hd ξ.1 ξ.2
    · refine (hc ξ.1 ξ.2).2.2.trans_eq ?_
      rw [hB]
      ring
  obtain ⟨hSum, hTot⟩ := hFreq n hn1 Q (K * B) g hle
  simp only [hg] at hSum hTot
  refine ⟨hSum, hTot.trans_eq ?_⟩
  rw [hB, hK]
  ring
end YangMills.Construction.ConfigSpace
