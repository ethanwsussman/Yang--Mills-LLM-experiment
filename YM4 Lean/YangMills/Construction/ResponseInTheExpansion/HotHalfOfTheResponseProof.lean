import YangMills.Construction.ResponseInTheExpansion.ForgettingOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.HotHalfOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.ScoredPriceReturns
import YangMills.Construction.ResponseInTheExpansion.ShapeOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheResponseReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses
theorem hotRegimeStep_holds (h₁ : ScoredPriceCoversCoarseScore) (h₂ : ResponseShapeStatement)
    (h₃ : StepDecayBoundsHold) (h₄ : StepSizeBoundsOfCold) :
    hotRegimeStepStatement := by
  obtain ⟨a₁, p₁, g₁⟩ := h₁
  obtain ⟨a₂, p₂, g₂⟩ := h₂
  obtain ⟨a₃, p₃, g₃⟩ := h₃
  obtain ⟨a₄, p₄, g₄⟩ := h₄
  refine ⟨fun c => min (min (a₁ c) (a₂ c)) (min (a₃ c) (a₄ c)),
    fun c => lt_min (lt_min (p₁ c) (p₂ c)) (lt_min (p₃ c) (p₄ c)), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hD (hrt.trans ((min_le_left _ _).trans (min_le_left _ _))) K
  obtain ⟨y₂, G₂⟩ := g₂ T hD (hrt.trans ((min_le_left _ _).trans (min_le_right _ _))) K
  obtain ⟨y₃, G₃⟩ := g₃ T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₄, G₄⟩ := g₄ T hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) K
  refine ⟨max (max y₁ y₂) (max y₃ y₄), fun y hy R A hK hAt hF hX hL => ?_⟩
  exact ⟨G₁ y ((le_max_left _ _).trans ((le_max_left _ _).trans hy)) R A hK hAt hF hX hL,
    G₂ y ((le_max_right _ _).trans ((le_max_left _ _).trans hy)) R A hK hAt hF hL,
    G₃ y ((le_max_left _ _).trans ((le_max_right _ _).trans hy)) R A hK hAt hF hL,
    G₄ y ((le_max_right _ _).trans ((le_max_right _ _).trans hy)) R A hK hAt hF hL⟩
end YangMills.Construction.ResponseInTheExpansion
end
