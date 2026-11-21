import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasAnExpansion
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusFields TorusLumps StepCosts BlockAverages WeightedResponses
def wilsonColdResponse (L : ℕ) : ColdResponse L 0 := fun _ _ y W h => siteResponse y W h
def wilsonHullResponse (L : ℕ) (Ω : Type) : HullResponse L 0 Ω := fun _ _ y W _ _ h => siteResponse y W h
def WilsonWeightHasResponseBoundsStatement : Prop :=
  ∃ C M : ℝ, ∀ (ℓ : StepParameters) (K : ResponseParameters), ℓ.Admissible → K.Admissible ℓ → C ≤ ℓ.derivBound →
    M * ℓ.weight 2 ≤ K.Kc →
    ∀ β : ℝ, ℓ.y₁ ≤ β → ∃ Λ : LabelSpace,
      HasResponseBoundsWith ℓ K 0 β 1 (wilsonWeight β) Λ (fun _ => 0) (wilsonColdResponse ℓ.side)
        (wilsonHullResponse ℓ.side Λ.Ω) (fun _ _ _ => 0) (fun _ _ _ => 0)
end ResponseInTheExpansion
end YangMills.Construction
end
