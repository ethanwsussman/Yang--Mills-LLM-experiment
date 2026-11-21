import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps
def wilsonWeightSingleLabelStatement : Prop :=
  ∃ C₀ : ℝ, ∀ P : StepParameters, P.Admissible → C₀ ≤ P.derivBound → ∀ β : ℝ, P.y₁ ≤ β →
    ∃ (Λ : LabelSpace) (point : Λ.Ω) (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
      (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ),
      (∀ ω : Λ.Ω, ω = point) ∧ Λ.μ {point} = 1 ∧
      (∀ (n : ℕ) [NeZero n] (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → Λ.Ω),
        Dq n W Y ω = open Classical in
          if Y = thickening (2 * clusterRange β) (torusHotSites P W) then wilsonWeight β n W else 0) ∧
      ColdExpansion P 0 β (wilsonWeight β) (fun _ _ _ => 0) ∧
      HullExpansion P 0 β (wilsonWeight β) (fun _ _ _ => 0) Λ Dq Φ (fun _ _ _ _ _ => 0)
end YangMills.Construction.WeightedResponses
end
