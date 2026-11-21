import YangMills.Construction.SummableBoundsOfTheFlow.ParametersHaveACouplingAboveOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SummableBounds
theorem couplingAtLeastOne : SummableBounds.couplingAtLeastOneStatement := by
  intro R hP a ha
  obtain ⟨L₀, hL⟩ := hP a ha
  refine ⟨L₀, fun L ho hg c hc => ?_⟩
  obtain ⟨Ct₀, h1⟩ := hL L ho hg c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ0, h2⟩ := h1 Ct hCt
  refine ⟨κ₀, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη0, h3⟩ := h2 κ hκ hκ'
  refine ⟨η₀, hη0, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₀, h4⟩ := h3 η₃ a1 a2 a3
  refine ⟨N₀, fun k hk => ?_⟩
  obtain ⟨σ₀, hσ0, h5⟩ := h4 k hk
  refine ⟨σ₀, hσ0, fun σ b1 b2 p hp => ?_⟩
  obtain ⟨C₀, h6⟩ := h5 σ b1 b2 p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h7⟩ := h6 Cs hCs E hE
  refine ⟨m₀, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h8⟩ := h7 n₀ hn₀
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h9⟩ := h8 CE hCE
  exact ⟨max 1 y₀, fun y hy => ⟨h9 y (le_trans (le_max_right _ _) hy),
    le_trans (le_max_left _ _) hy⟩⟩
end YangMills.Construction.SummableBounds
end
