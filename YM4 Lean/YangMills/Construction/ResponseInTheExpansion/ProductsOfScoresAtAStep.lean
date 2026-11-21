import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepCosts BlockAverages WeightedResponses LumpContours
def MeanOfScoreProductsStatement : Prop :=
  ∀ (ℓ : StepParameters) (x : ℝ) (n : ℕ) [NeZero n] (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n) (m : ℕ)
    (a : Fin m → ℝ) (v : Fin m → TorusBond n → ℝ),
    (∀ (c : TorusBond n) (i j : Fin m), i ≠ j → v i c = 0 ∨ v j c = 0) →
    ∫ V : TorusField n, (∏ i, (a i + ∑ c : TorusBond n, v i c * bondScore ℓ x W V b c)) *
        ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
          bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c
      ∂(fieldHaar n) = ∏ i, a i
end YangMills.Construction.ResponseInTheExpansion
end
