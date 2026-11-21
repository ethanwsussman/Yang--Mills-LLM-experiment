import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.FieldAboveTheFrameIsCold
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.MovingTheChartCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem fieldAboveFrameSmallCurvature_holds (hW : frameBoundsStatement)
    (hC : CouplingThreshold) (hM : ChartShiftLipschitz) :
    fieldAboveFrameSmallCurvature := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hLe c hc => ?_⟩
  obtain ⟨Cf, C, σ₀, hF⟩ := hW a L c ha hL hLe hc
  obtain ⟨-, -, hσ₀, hF⟩ := hF
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct _ => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun nss _ => ⟨σ₀, hσ₀, fun σ hσ hσ' p _ => ⟨0, fun Cs _ E _ =>
      ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨y₀, hy⟩ := hC Cf C c.δ₂ κ σ 0 hδ₂ hκ hκ' hσ
  refine ⟨max y₀ 1, fun y₁ hy₁ t x hx F hT V hV η hη => ?_⟩
  have hxy : y₁ ≤ x := hx
  have hx0 : y₀ ≤ x := le_trans (le_trans (le_max_left _ _) hy₁) hxy
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) hy₁) hxy
  obtain ⟨-, h16, hg, hxω, hxe, -⟩ := hy x hx0
  have hsmall := (hF κ σ x (frameRadius x) t n₀ hκ hκ' hσ hσ' hx1 h16 hn₀ hg hxω hxe F V hT hV).2.1
    false
  have hodd : Odd F.blockSide := by
    rw [hT.1]
    exact hL
  have hr : (0 : ℝ) ≤ σ / 64 := by positivity
  have hm := (hM F V (frameCoordField false a c.ρA (frameRadius x) V) η (σ / 64) hodd hη hr).2.1
  intro q hq
  have h1 := hm q
  have h2 := hsmall.small_curvature q hq
  have h3 : plaquetteDefect (fieldAboveFrame false a c.ρA (frameRadius x) V η) q ≤
      plaquetteDefect (chartedField (frameCoordField false a c.ρA (frameRadius x) V) V) q + 4 * (σ / 64) := h1
  simp only [Bool.false_eq_true, if_false] at h2
  show plaquetteDefect (fieldAboveFrame false a c.ρA (frameRadius x) V η) q < σ
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
