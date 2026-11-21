import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAboveLevelZero
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainOneLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
variable {F F' : BlockFrame}
private theorem coldEstimatesBelow_mono {a δ s : ℝ} {N N' : ℕ → ℝ} {W : F.GaugeField F.depth}
    (h : ColdEstimatesBelow a δ s N W) (hs : 0 ≤ s)
    (hN : ∀ k, N k ≤ N' k) : ColdEstimatesBelow a δ s N' W where
  minimalAction_analytic := h.minimalAction_analytic
  siteShare_analytic := h.siteShare_analytic
  chainShare_eq := h.chainShare_eq
  minimalAction_deriv_decay := fun k c X hk hX =>
    (h.minimalAction_deriv_decay k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
  minimalAction_firstDeriv_le := fun c X hX =>
    (h.minimalAction_firstDeriv_le c X hX).trans (mul_le_mul_of_nonneg_right (hN 1) hs)
  siteShare_deriv_decay := fun y k c X hk hX =>
    (h.siteShare_deriv_decay y k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
  siteShare_bounds := fun y => ⟨(h.siteShare_bounds y).1,
    (h.siteShare_bounds y).2.trans (mul_le_mul_of_nonneg_right (hN 0) (sq_nonneg s))⟩
  siteShare_firstDeriv_le := fun y c X hX => (h.siteShare_firstDeriv_le y c X hX).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN 1) hs) (Real.exp_pos _).le)
  siteShare_gauge_invariant := h.siteShare_gauge_invariant
  siteShare_translate := h.siteShare_translate
private theorem coldComparisonBelow_mono {a δ δ₂ s s₀ : ℝ} {N N' : ℕ → ℝ} {W : F.GaugeField F.depth}
    {W' : F'.GaugeField F'.depth} {y : F.Site F.depth} {y' : F'.Site F'.depth} {r : ℕ}
    (h : ColdComparisonBelow a δ δ₂ s s₀ N W W' y y' r) (hs : 0 ≤ s)
    (hN : ∀ k, N k ≤ N' k) : ColdComparisonBelow a δ δ₂ s s₀ N' W W' y y' r where
  siteShare_deriv_close := fun k q X hq hX => (h.siteShare_deriv_close k q X hq hX).trans (by
    have hf : 0 ≤ derivativeScale s k := by
      unfold derivativeScale
      split_ifs <;> positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hN k) hf) (Real.exp_pos _).le)
  minimalAction_firstDeriv_close := fun hs0 b X hb hX => (h.minimalAction_firstDeriv_close hs0 b X hb hX).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN 0) hs) (Real.exp_pos _).le)
theorem coldEstimatesAtEveryDepth_of_positiveDepth (hA : ColdEstimatesAtPositiveDepth)
    (hZ : WilsonActionColdEstimates) : ColdEstimatesAtEveryDepth := by
  intro a L c ha hL hL40 hc
  obtain ⟨N₁, hN₁, hh₁, hc₁⟩ := hA a L c ha hL hL40 hc
  obtain ⟨N₀, hN₀, hz⟩ := hZ
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  obtain ⟨hz₁, hz₂⟩ := hz a c.δ₁ c.δ₂ c.s₀ hc.positivity.1.le hc.inequalities.1 hδ₂.le
  have m₁ : ∀ k, N₁ k ≤ N₁ k + N₀ k := fun k => by
    have := hN₀ k
    linarith
  have m₀ : ∀ k, N₀ k ≤ N₁ k + N₀ k := fun k => by
    have := hN₁ k
    linarith
  refine ⟨fun k => N₁ k + N₀ k, fun k => add_pos (hN₁ k) (hN₀ k), ?_, ?_⟩
  · intro F s W hT hs hsσ hW
    rcases Nat.eq_zero_or_pos F.depth with ht | ht
    · exact coldEstimatesBelow_mono (hz₁ F s W ht (hT.1 ▸ hL) hT.2 hs hW) hs.le m₀
    · exact coldEstimatesBelow_mono (hh₁ F s W hT ht hs hsσ hW) hs.le m₁
  · intro F F' s W W' y y' r hT hT' ht hs hsσ hW hW' hag
    rcases Nat.eq_zero_or_pos F.depth with h0 | h0
    · exact coldComparisonBelow_mono
        (hz₂ F F' s W W' y y' r h0 (ht.trans h0) (hT.1 ▸ hL) (hT'.1 ▸ hL) hT.2 hT'.2 hs hW hW' hag) hs.le m₀
    · exact coldComparisonBelow_mono (hc₁ F F' s W W' y y' r hT hT' h0 ht hs hsσ hW hW' hag) hs.le m₁
end YangMills.Construction.ColdStepAtMirrorFrames
end
