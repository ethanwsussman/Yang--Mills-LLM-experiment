import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def ConstantCurvatureMinimalAction : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → c.Admissible a L → ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ), F.blockSide = L →
      (∀ i, F.extent i = n) → 64 ≤ n → ‖X‖ = 1 → μ < ν →
      2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      (∀ j, j < F.top →
        (∀ W' : F.GaugeField j,
          blockEnergy a (finiteCells F) j (constantCurvatureChain F X μ ν l j)
              (constantCurvatureChain F X μ ν l (j + 1)) ≤
            blockEnergy a (finiteCells F) j W' (constantCurvatureChain F X μ ν l (j + 1))) ∧
        minimalAction a (finiteCells F) (j + 1) (constantCurvatureChain F X μ ν l (j + 1)) =
          minimalAction a (finiteCells F) j (constantCurvatureChain F X μ ν l j)) ∧
      minimalAction a (finiteCells F) F.top (constantCurvatureChain F X μ ν l F.top) =
        ((n : ℝ) * (L : ℝ) ^ F.top) ^ 4 *
          (1 - Real.cos (2 * Real.pi * l / ((n : ℝ) * (L : ℝ) ^ F.top) ^ 2))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
