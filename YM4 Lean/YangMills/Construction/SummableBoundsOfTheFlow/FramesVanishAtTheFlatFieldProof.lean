import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAtTheFlatTop
import YangMills.Construction.SummableBoundsOfTheFlow.FramesVanishAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SummableBounds
theorem framesVanishAtFlat (h : ColdStepAtMirrorFrames.stepFramesAtUniformTop)
    (hC : ColdStepAtMirrorFrames.CouplingThreshold) : SummableBounds.framesVanishAtFlatStatement := by
  intro a ha
  refine ⟨0, fun L hL _ c hc => ?_⟩
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct _ => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun k _ => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E _ =>
      ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨y₀, hy⟩ := hC 1 1 c.δ₂ κ σ 0 hδ₂ hκ hκ' hσ
  refine ⟨y₀, fun y hy₁ t x F U hx hF => ?_⟩
  have h16 : 16 ≤ ColdStepAtMirrorFrames.frameRadius x := (hy x (hy₁.trans hx)).2.1
  obtain ⟨hFL, _, n, hn, hnn⟩ := hF
  have hcub : BlockAverages.IsLargeCubicTorus F := ⟨n, hn₀.trans hnn, hn⟩
  have key := h a L c (ColdStepAtMirrorFrames.frameRadius x) ha hL hc h16 F U ⟨hFL, hcub⟩
  exact ⟨fun b _ => key.1 b, key.2⟩
end YangMills.Construction.SummableBounds
end
