import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields
namespace ColdStepAtMirrorFrames
def ExpansionAtMinimizingChainField : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters) (σ δ E E₃ : ℝ) (t n₀ m : ℕ) (f : LocalFamily), 1 ≤ a → Odd L →
    c.Admissible a L → 0 < σ →
    IsRegularFamily L t n₀ σ δ E E₃ f → ∃ γ₁ : ℝ, 0 < γ₁ ∧
      ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ), 64 ≤ n → n₀ ≤ n * L → ‖X‖ = 1 →
      μ < ν → 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₁ → ∀ y : (torusFrame L t n).Site (torusFrame L t n).depth,
        centredExpansion true a c.ρA m f y 0 (constantCurvatureChain (torusFrame L t n) X μ ν l (torusFrame L t n).top) =
          subtractTrivial f (torusFrame L t n) y
            (constantCurvatureChain (torusFrame L t n) X μ ν l (torusFrame L t n).depth)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
