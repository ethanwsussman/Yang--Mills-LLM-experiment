import YangMills.Construction.TorusOrFourSpace.EffectiveConstantsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.FactsOnTheRadiusThetaAndUnitFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def EffectiveConstantFacts.Claim : Prop :=
  ThetaNumberGeOne ∧
    (∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (a : P.Idx),
      IsLipschitzQ D torus (P.bump a)) ∧
    (∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (E : Kind)
      (C : BoundFamily) (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
      effConstAt P E C n d R ∈ Set.Ici (0 : ℝ)) ∧
    (∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (C : BoundFamily)
      (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
      effConstAt P euclidean C n d R = C.val n d R) ∧
    RadiusThetaDependence
end YangMills.Construction.PeriodicSpace
end
