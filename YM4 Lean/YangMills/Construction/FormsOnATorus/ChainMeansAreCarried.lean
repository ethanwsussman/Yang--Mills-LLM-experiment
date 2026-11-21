import YangMills.Construction.FormsOnATorus.MeansOfAFieldDownTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
def ChainExpectationsTransported : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (x : ℕ → ℝ) (s n : ℕ) [NeZero n], ℓ.n₀ ≤ n →
    ∀ (g : TorusIsometry) (F F' : TorusField n → ENNReal),
    Measurable F → Measurable F' → (∀ V V', g.Transports V V' → F' V' = F V) →
      ∀ U U', (iteratedScaledLift ℓ.side s g).Transports U U' →
      chainExpectation ℓ x s n F' U' = chainExpectation ℓ x s n F U
end YangMills.Construction.WeightedResponses
end
