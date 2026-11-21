import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionDensityBoundsForm
import YangMills.Construction.ColdStepAtMirrorFrames.SizesOfTheExpansionDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private lemma eventuallyInParameters_mono {P Q : StepParameters → Prop} (hPQ : ∀ T, 0 < T.σ → P T → Q T)
    (H : EventuallyInParameters P) : EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h⟩ := H a ha
  refine ⟨L₀, fun L hL hLe c hc => ?_⟩
  obtain ⟨Ct₀, h⟩ := h L hL hLe c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := h κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ h1 h2 h3 => ?_⟩
  obtain ⟨N₀, h⟩ := h η₃ h1 h2 h3
  refine ⟨N₀, fun nss hn => ?_⟩
  obtain ⟨σ₀, hσ₀, h⟩ := h nss hn
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h⟩ := h σ hσ hσ' p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h⟩ := h Cs hCs E hE
  refine ⟨m₀, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h⟩ := h n₀ hn₀
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h⟩ := h CE hCE
  exact ⟨y₀, fun y₁ hy₁ => hPQ _ hσ (h y₁ hy₁)⟩
theorem expansionDensityBounds_holds (hB : stepDensityDerivBoundsStatement) :
    expansionDensityBoundsStatement := by
  refine eventuallyInParameters_mono (fun T hσ H t x hx f hf => ?_) hB
  obtain ⟨hd, hl⟩ := H t x f hx hf
  refine ⟨fun F hF Y V k c X hV h1 h3 hX => hd F hF Y V k c X
    (fun p hp => lt_of_lt_of_le (hV p hp) (by linarith)) h1 h3 hX, hl⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
