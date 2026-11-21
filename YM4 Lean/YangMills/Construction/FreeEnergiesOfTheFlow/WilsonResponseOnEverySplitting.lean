import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FreeEnergiesOfTheFlow
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion
def WilsonResponseEverySplitting : Prop :=
  ∃ M : ℝ, ∀ (ℓ : StepParameters) (K : ResponseParameters), ℓ.Admissible → K.Admissible ℓ → M * ℓ.weight 2 ≤ K.Kc →
    ∀ β : ℝ, ℓ.y₁ ≤ β →
    ∀ (f : LocalDensity) (Λ : LabelSpace) (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
      (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
      (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ),
      HullExpansion ℓ 0 β (wilsonWeight β) f Λ Dq Φ φ →
        PriceBoundsScore ℓ β Λ Φ φ (fun _ => 0) ∧
          ResponseBounds ℓ K 0 β 1 Λ Dq (fun _ => 0) (wilsonColdResponse ℓ.side) (wilsonHullResponse ℓ.side Λ.Ω)
            (fun _ _ _ => 0) (fun _ _ _ => 0)
end FreeEnergiesOfTheFlow
end YangMills.Construction
end
