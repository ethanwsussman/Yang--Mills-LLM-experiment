import YangMills.Construction.ColdStepAtMirrorFrames.TransportParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages Filter Topology
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
namespace TransportConditions
theorem tendsto_exp_tails_atTop {δ b A : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.exp (-(δ * x)) + (1 + A * x ^ 16000) * Real.exp (-(b * x))) atTop (𝓝 0) := by
  have hexp : ∀ {c : ℝ}, 0 < c → Tendsto (fun x : ℝ => Real.exp (-(c * x))) atTop (𝓝 0) := fun hc =>
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc))
  have hpow : Tendsto (fun x : ℝ => x ^ 16000 * Real.exp (-(b * x))) atTop (𝓝 0) := by
    have := (isLittleO_pow_exp_pos_mul_atTop 16000 hb).tendsto_div_nhds_zero
    refine this.congr fun x => ?_
    rw [Real.exp_neg, div_eq_mul_inv]
  have hsum := (hexp hδ).add ((hexp hb).add (hpow.const_mul A))
  simp only [add_zero, mul_zero] at hsum
  refine hsum.congr fun x => ?_
  ring
theorem div_pow_eq_inv_pow_mul (K : ℕ) (n N : ℝ) : (n / N) ^ K = (1 / N) ^ K * n ^ K := by
  have hdiv : n / N = (1 / N) * n := by ring
  rw [hdiv, mul_pow]
theorem torusDecayFactor_mul_tails_le {L : ℕ} {δ κ : ℝ} (hL : 32 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ κ) (n : ℕ) :
    torusDecayFactor L δ n * (1 / torusDecayFactor L δ ((L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * κ * n))) ≤
      Real.exp (-(δ * n)) + (1 + (1 / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 * (n : ℝ) ^ 16000) * Real.exp (-(κ * n)) := by
  have hLr : (32 : ℝ) ≤ L := by exact_mod_cast hL
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set N := (L : ℝ) ^ (1 / 640 : ℝ) with hN
  set M := max 1 (((n : ℝ) / N) ^ 16000) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMle : M ≤ 1 + (1 / N) ^ 16000 * (n : ℝ) ^ 16000 := by
    have e : ((n : ℝ) / N) ^ 16000 = (1 / N) ^ 16000 * (n : ℝ) ^ 16000 := div_pow_eq_inv_pow_mul 16000 n N
    rw [hM, max_le_iff, e]
    have : 0 ≤ (1 / N) ^ 16000 * (n : ℝ) ^ 16000 :=
      mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg hn _)
    constructor <;> linarith
  have hx : (n : ℝ) ≤ (L : ℝ) * n / 16 := by nlinarith
  have hx2 : 2 * (n : ℝ) ≤ (L : ℝ) * n / 16 := by nlinarith
  have hM2 : M ≤ max 1 ((((L : ℝ) * n / 16) / N) ^ 16000) := by
    refine max_le_max le_rfl ?_
    exact pow_le_pow_left₀ (by positivity) (by gcongr) _
  have hG : torusDecayFactor L δ n = M * Real.exp (δ * n) := rfl
  have h1 : torusDecayFactor L δ n * (1 / torusDecayFactor L δ ((L : ℝ) * n / 16)) ≤ Real.exp (-(δ * n)) := by
    have hGb : M * Real.exp (δ * (2 * n)) ≤ torusDecayFactor L δ ((L : ℝ) * n / 16) := by
      unfold torusDecayFactor
      refine mul_le_mul hM2 (Real.exp_le_exp.mpr (by gcongr)) (Real.exp_pos _).le
        (le_trans zero_le_one (le_max_left _ _))
    have hpos : 0 < M * Real.exp (δ * (2 * n)) := by positivity
    rw [hG, mul_one_div, div_le_iff₀ (lt_of_lt_of_le hpos hGb)]
    calc M * Real.exp (δ * n) = Real.exp (-(δ * n)) * (M * Real.exp (δ * (2 * n))) := by
          have e3 : Real.exp (δ * n) = Real.exp (-(δ * n)) * Real.exp (δ * (2 * n)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [e3]
          ring
      _ ≤ _ := by gcongr
  have h2 : torusDecayFactor L δ n * Real.exp (-(2 ^ 6 * κ * n)) ≤
      (1 + (1 / N) ^ 16000 * (n : ℝ) ^ 16000) * Real.exp (-(κ * n)) := by
    rw [hG, mul_assoc, ← Real.exp_add]
    have : δ * n + -(2 ^ 6 * κ * n) ≤ -(κ * n) := by
      have hκ : 0 < κ := lt_of_lt_of_le hδ0 hδ
      nlinarith [mul_nonneg hκ.le hn, mul_le_mul_of_nonneg_right hδ hn]
    exact mul_le_mul hMle (Real.exp_le_exp.mpr this) (Real.exp_pos _).le (by linarith)
  rw [mul_add]
  exact add_le_add h1 h2
end TransportConditions
open TransportConditions
theorem transportConditionsEventually_holds : transportConditionsEventually := by
  intro Q a ha
  refine ⟨2 ^ 40, fun L hLo hL c hc => ?_⟩
  refine ⟨1, fun Ct hCt => ?_⟩
  refine ⟨1, one_pos, fun κ hκ _ => ?_⟩
  have hCt0 : 0 < Ct := by linarith
  have hδ0 : 0 < κ / 2 ^ 10 := by positivity
  have hδκ : κ / 2 ^ 10 ≤ κ := by
    have : κ / 2 ^ 10 = κ * (1 / 2 ^ 10) := by ring
    rw [this]
    nlinarith
  have h32 : 32 ≤ L := le_trans (by norm_num) hL
  have hev := (tendsto_exp_tails_atTop (A := (1 / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) hδ0 hκ).comp
    tendsto_natCast_atTop_atTop
  have hsm : ∀ᶠ n : ℕ in atTop, Real.exp (-(κ / 2 ^ 10 * n)) +
      (1 + (1 / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 * (n : ℝ) ^ 16000) * Real.exp (-(κ * n)) <
      1 / (2 ^ 10 * ((L : ℝ) ^ 4 * Ct)) :=
    hev.eventually (gt_mem_nhds (by positivity))
  obtain ⟨ns, hns⟩ := eventually_atTop.mp hsm
  have hfar0 : ∀ n : ℕ, ns ≤ n → 2 ^ 10 * ((L : ℝ) ^ 4 * Ct) * torusDecayFactor L (κ / 2 ^ 10) n *
      (1 / torusDecayFactor L (κ / 2 ^ 10) ((L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * κ * n))) ≤ 1 := by
    intro n hn
    have h1 := torusDecayFactor_mul_tails_le h32 hδ0 hδκ n
    have h2 := hns n hn
    have h3 := h1.trans h2.le
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith
  let U : StepParameters := ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  have hex : ∃ ns : ℕ, ∀ n : ℕ, ns ≤ n → 2 ^ 10 * ((U.L : ℝ) ^ 4 * U.Ct) * torusDecayFactor U.L U.decayRate n *
      (1 / torusDecayFactor U.L U.decayRate ((U.L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * U.κ * n))) ≤ 1 := ⟨ns, hfar0⟩
  have hfar : ∀ n : ℕ, decayThresholdIndex U ≤ n → 2 ^ 10 * ((L : ℝ) ^ 4 * Ct) * torusDecayFactor L (κ / 2 ^ 10) n *
      (1 / torusDecayFactor L (κ / 2 ^ 10) ((L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * κ * n))) ≤ 1 := by
    intro n hn
    unfold decayThresholdIndex at hn
    rw [dif_pos hex] at hn
    exact hex.choose_spec n hn
  refine ⟨2⁻¹ ^ 9 / (|Q U| + 1), by positivity, fun η₃ hη hη1 hη0 => ?_⟩
  refine ⟨decayThresholdIndex U, fun nss hnss => ?_⟩
  refine ⟨1, one_pos, fun σ hσ _ p hp => ?_⟩
  refine ⟨0, fun Cs _ E hE => ?_⟩
  refine ⟨8 * nss + 8, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨0, fun y₁ _ => ?_⟩
  refine ⟨⟨ha, hLo, hc, hκ, hη, hη1, hσ, hp, hE⟩, hL, hCt0, hn₀, hnss, hfar, ?_⟩
  show Q U * η₃ ≤ 2⁻¹ ^ 9
  rw [le_div_iff₀ (by positivity)] at hη0
  have h1 := le_abs_self (Q U)
  have h2 := abs_nonneg (Q U)
  nlinarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
