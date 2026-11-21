import YangMills.Construction.ClusterExpansionOfAStep.TranslationsCarryTheKernelAtBases
import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepCosts BaseTranslations WeightedResponses BlockAverages
namespace BondScores
def BondScoreTranslationInvariant : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n], ℓ.n₀ ≤ n →
    ∀ (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n), b ∈ baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) →
    bondScore ℓ x (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)
        (TorusFields.translate (siteOfInt v) V)
        (translateBases v b) (c.1 - siteOfInt v, c.2) =
      bondScore ℓ x W V b c
end BondScores
end YangMills.Construction
end
