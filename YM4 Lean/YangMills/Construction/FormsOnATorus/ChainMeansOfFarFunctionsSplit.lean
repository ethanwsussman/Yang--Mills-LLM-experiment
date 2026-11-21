import YangMills.Construction.FormsOnATorus.MeansOfAFieldDownTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
def ChainExpectationsFactorizeForSeparatedCells : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side →
    ∀ (x : ℕ → ℝ) (s n c M r : ℕ) [NeZero n], n = c * M → 16 ≤ n →
    2 * r + 9 ≤ c → ∀ (u : Fin 4 → ℤ) (F : (Fin 4 → Fin M) → TorusField n → ENNReal),
      (∀ k, Measurable (F k)) →
      (∀ k, DependsOnlyNear (siteOfInt fun i => u i + c * ((k i : ℕ) : ℤ)) r (F k)) →
      (∀ U, chainExpectation ℓ x s n (fun V => ∏ k, F k V) U = ∏ k, chainExpectation ℓ x s n (F k) U) ∧
      ∀ k, DependsOnlyNear (siteOfInt fun i => (ℓ.side : ℤ) ^ s * (u i + c * ((k i : ℕ) : ℤ)))
        (descendedRadius ℓ.side s r) (chainExpectation ℓ x s n (F k))
end YangMills.Construction.WeightedResponses
end
