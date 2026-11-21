import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
def HaarGapExcessBounded : Prop :=
  ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (F : BlockFrame) (a x : ℝ) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4),
    Odd F.blockSide → 1 ≤ a → 2 ≤ x →
    (∀ (h : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c h σ - 1‖ ≤ 1 / 2) →
    |haarGapExcess a x W c| ≤ Cg
end ScaledVariables
end YangMills.Construction
end
