import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def stepFramesAtUniformTop : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters) (m : ℕ), 1 ≤ a → Odd L → c.Admissible a L → 16 ≤ m →
    ∀ (F : BlockFrame) (starred : Bool), IsBlockTorus L F →
      (∀ b : F.Site F.depth × Fin 4, stepFrame starred a c.ρA m b (uniformField F F.top) = 0) ∧
      fieldAboveFrame starred a c.ρA m (uniformField F F.top) 0 = uniformField F F.depth
end ColdStepAtMirrorFrames
end YangMills.Construction
end
