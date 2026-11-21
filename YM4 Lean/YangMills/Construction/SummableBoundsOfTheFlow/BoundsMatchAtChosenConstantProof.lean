import YangMills.Construction.SummableBoundsOfTheFlow.BoundsMatchAtChosenConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SummableBounds
theorem joinAtLoweredSmallnessConstant : SummableBounds.joinAtLoweredSmallnessConstantStatement := by
  intro P R Q G hP hR h a ha
  obtain ⟨L₁, p₁⟩ := hP a ha
  obtain ⟨L₂, r₁⟩ := hR a ha
  refine ⟨max L₁ L₂, fun L ho hg c hc => ?_⟩
  obtain ⟨A₁, p₂⟩ := p₁ L ho (le_trans (le_max_left _ _) hg) c hc
  obtain ⟨A₂, r₂⟩ := r₁ L ho (le_trans (le_max_right _ _) hg) c hc
  refine ⟨max A₁ A₂, fun Ct hCt => ?_⟩
  obtain ⟨k₁, hk₁, p₃⟩ := p₂ Ct (le_trans (le_max_left _ _) hCt)
  obtain ⟨k₂, hk₂, r₃⟩ := r₂ Ct (le_trans (le_max_right _ _) hCt)
  refine ⟨min k₁ k₂, lt_min hk₁ hk₂, fun κ hκ hκ' => ?_⟩
  obtain ⟨e₁, he₁, p₄⟩ := p₃ κ hκ (le_trans hκ' (min_le_left _ _))
  obtain ⟨e₂, he₂, r₄⟩ := r₃ κ hκ (le_trans hκ' (min_le_right _ _))
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₁, p₅⟩ := p₄ η₃ a1 a2 (le_trans a3 (min_le_left _ _))
  obtain ⟨N₂, r₅⟩ := r₄ η₃ a1 a2 (le_trans a3 (min_le_right _ _))
  refine ⟨max N₁ N₂, fun k hn => ?_⟩
  obtain ⟨s₁, hs₁, p₆⟩ := p₅ k (le_trans (le_max_left _ _) hn)
  obtain ⟨s₂, hs₂, r₆⟩ := r₅ k (le_trans (le_max_right _ _) hn)
  refine ⟨min s₁ s₂, lt_min hs₁ hs₂, fun σ b1 b2 q hq => ?_⟩
  obtain ⟨C₁, p₇⟩ := p₆ σ b1 (le_trans b2 (min_le_left _ _)) q hq
  obtain ⟨C₂, r₇⟩ := r₆ σ b1 (le_trans b2 (min_le_right _ _)) q hq
  set u : ℝ := max 1 (max C₁ C₂) with hu
  have hu1 : 1 ≤ u := le_max_left _ _
  have huC₁ : C₁ ≤ u := le_trans (le_max_left _ _) (le_max_right _ _)
  have huC₂ : C₂ ≤ u := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨G ⟨a, L, c, Ct, κ, η₃, k, σ, q, 0, 0, 0, 0, 0⟩ u, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₁, p₈⟩ := p₇ u huC₁ E hE
  obtain ⟨m₂, r₈⟩ := r₇ u huC₂ E hE
  refine ⟨max 1 (max m₁ m₂), fun n₀ hn₀ => ?_⟩
  have hn1 : 1 ≤ n₀ := le_trans (le_max_left _ _) hn₀
  have hn₂ : max m₁ m₂ ≤ n₀ := le_trans (le_max_right _ _) hn₀
  obtain ⟨D₁, p₉⟩ := p₈ n₀ (le_trans (le_max_left _ _) hn₂)
  obtain ⟨D₂, r₉⟩ := r₈ n₀ (le_trans (le_max_right _ _) hn₂)
  refine ⟨max D₁ D₂, fun CE hCE => ?_⟩
  obtain ⟨y₁, p₁₀⟩ := p₉ CE (le_trans (le_max_left _ _) hCE)
  obtain ⟨y₂, r₁₀⟩ := r₉ CE (le_trans (le_max_right _ _) hCE)
  refine ⟨max 1 (max y₁ y₂), fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
  have hy₂ : max y₁ y₂ ≤ y := le_trans (le_max_right _ _) hy
  exact h ⟨a, L, c, Ct, κ, η₃, k, σ, q, Cs, E, n₀, CE, y⟩ u hu1 ho hn1 hy1 hE a1 a2 hκ b1 hc hq hCs
    (p₁₀ y (le_trans (le_max_left _ _) hy₂)) (r₁₀ y (le_trans (le_max_right _ _) hy₂))
end YangMills.Construction.SummableBounds
end
