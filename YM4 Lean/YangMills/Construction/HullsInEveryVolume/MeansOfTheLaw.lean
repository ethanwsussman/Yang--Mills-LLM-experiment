import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.TiltedSquares
theorem measurable_sigma_of_fibres {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
end YangMills.Construction.TiltedSquares
