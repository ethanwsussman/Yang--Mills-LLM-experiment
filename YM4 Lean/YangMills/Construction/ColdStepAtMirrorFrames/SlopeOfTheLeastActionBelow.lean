import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def MinimalActionDerivComparison : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth) (y : F.Site F.depth)
        (y' : F'.Site F'.depth) (R : ℕ),
        IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth → IsSmallCurvature c.s₀ W →
        IsSmallCurvature c.s₀ W' → AgreeOnBox W W' y y' R → 2 ≤ R → ∀ (i : Fin 4) (X : imaginaryQuaternions), ‖X‖ = 1 →
          |bondDeriv (minimalAction a (finiteCells F) F.depth) W ![(y, i)] ![X] -
            bondDeriv (minimalAction a (finiteCells F') F'.depth) W' ![(y', i)] ![X]| ≤
            C * Real.exp (-(c.δ₂ * R))
end YangMills.Construction.ColdStepAtMirrorFrames
end
